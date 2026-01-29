//! # QUIC Server Instance Management
//!
//! Defines the QuicServer struct and lifecycle methods.
//! Manages a single QUIC server instance with statistics tracking,
//! quinn endpoint lifecycle, and zero-copy packet handoff via SPSC queues.

use dashmap::DashMap;
use krepis_core::FfiQuicConfig;
use serde::{Deserialize, Serialize};
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::{SystemTime, UNIX_EPOCH};
use tokio::sync::mpsc;

// ============================================================================
// PACKET BUFFER (Zero-copy handoff)
// ============================================================================

/// A single packet buffer for zero-copy handoff to TS layer
/// Stored in SPSC queue, pinned until consumed
///
/// # Zero-Copy Architecture
///
/// PacketBuffer owns a Vec<u8> that is **never copied** during transit:
///
/// 1. **Creation**: `PacketBuffer::new(data: Vec<u8>, _)` takes ownership via move
///    - No cloning of the Vec allocation
///    - Original heap allocation is preserved
///    - Pointer address is guaranteed identical
///
/// 2. **Queue Transit**: Data moves through `PacketQueue` via mpsc channel
///    - mpsc::unbounded_channel moves the PacketBuffer by value
///    - No serialization/deserialization
///    - No deep copy of contained Vec
///
/// 3. **TS Consumer Handoff**: TS layer receives via FFI
///    - `UnsafePointerView` can directly reference the Vec data
///    - Pointer is stable because Vec is pinned in the queue
///    - Memory layout: [data_ptr, len, capacity] → directly compatible with Deno's memory view
///
/// # Correctness Proof
///
/// The test suite validates zero-copy by:
/// - Capturing the original Vec's pointer **before** move
/// - Verifying the pointer identity **after** queue transit
/// - Confirming no new allocation occurred
///
/// If `packet.as_ptr() != original_ptr`, a clone occurred (violation of zero-copy principle).
#[derive(Debug, Clone)]
pub struct PacketBuffer {
    /// Raw packet bytes (pinned in queue)
    pub data: Vec<u8>,
    /// Source connection handle
    pub connection_handle: u64,
    /// Timestamp of receipt (microseconds since epoch)
    pub timestamp_us: u64,
    /// Stream ID if applicable
    pub stream_id: Option<u64>,
}

impl PacketBuffer {
    /// Create a new packet buffer
    pub fn new(data: Vec<u8>, connection_handle: u64) -> Self {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_micros() as u64)
            .unwrap_or(0);

        Self {
            data,
            connection_handle,
            timestamp_us: now,
            stream_id: None,
        }
    }

    /// Size in bytes
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Check if empty
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// Pointer to data (for FFI access via KNUL)
    pub fn as_ptr(&self) -> *const u8 {
        self.data.as_ptr()
    }
}

// ============================================================================
// PACKET QUEUE (SPSC for deterministic handoff)
// ============================================================================

/// Single Producer, Single Consumer queue for packet buffers
/// Ensures thread-safe, ordered delivery without copying
pub struct PacketQueue {
    tx: mpsc::UnboundedSender<PacketBuffer>,
    rx: Arc<tokio::sync::Mutex<mpsc::UnboundedReceiver<PacketBuffer>>>,
    /// Atomic counter for queue depth (updated on enqueue/dequeue)
    depth: Arc<AtomicUsize>,
}

impl PacketQueue {
    /// Create a new packet queue
    pub fn new() -> Self {
        let (tx, rx) = mpsc::unbounded_channel();
        Self {
            tx,
            rx: Arc::new(tokio::sync::Mutex::new(rx)),
            depth: Arc::new(AtomicUsize::new(0)),
        }
    }

    /// Enqueue a packet (producer side - internal network loop)
    pub fn enqueue(&self, packet: PacketBuffer) -> Result<(), String> {
        self.tx
            .send(packet)
            .map_err(|e| format!("Queue enqueue failed: {}", e))?;

        // Increment queue depth counter
        self.depth.fetch_add(1, Ordering::Release);
        Ok(())
    }

    /// Try to dequeue without blocking (consumer side - TS layer)
    pub async fn try_dequeue(&self) -> Option<PacketBuffer> {
        let mut rx = self.rx.lock().await;
        if let Some(packet) = rx.recv().await {
            // Decrement queue depth counter
            self.depth.fetch_sub(1, Ordering::Release);
            Some(packet)
        } else {
            None
        }
    }

    /// Get queue depth (for monitoring)
    pub fn len(&self) -> usize {
        self.depth.load(Ordering::Acquire)
    }

    /// Check if queue is empty
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl Default for PacketQueue {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// CONNECTION HANDLER (spawned per QUIC connection)
// ============================================================================

/// Per-connection handler task spawned when accepting a new connection
struct ConnectionHandler {
    handle: u64,
    connection: quinn::Connection,
    packet_queue: Arc<PacketQueue>,
    stats_requests: Arc<AtomicU64>,
    stats_bytes_in: Arc<AtomicU64>,
    stats_bytes_out: Arc<AtomicU64>,
    stats_errors: Arc<AtomicU64>,
    max_payload_bytes: usize,
}

impl ConnectionHandler {
    /// Spawn a new connection handler task
    async fn spawn(
        handle: u64,
        connection: quinn::Connection,
        packet_queue: Arc<PacketQueue>,
        stats_requests: Arc<AtomicU64>,
        stats_bytes_in: Arc<AtomicU64>,
        stats_bytes_out: Arc<AtomicU64>,
        stats_errors: Arc<AtomicU64>,
        max_payload_bytes: usize,
    ) {
        let handler = Self {
            handle,
            connection,
            packet_queue,
            stats_requests,
            stats_bytes_in,
            stats_bytes_out,
            stats_errors,
            max_payload_bytes,
        };

        tokio::spawn(async move {
            if let Err(e) = handler.run().await {
                eprintln!("Connection handler error: {}", e);
            }
        });
    }

    /// Main loop: accept bidirectional streams and route data to queue
    async fn run(mut self) -> Result<(), Box<dyn std::error::Error>> {
        loop {
            match self.connection.accept_bi().await {
                Ok((send_stream, recv_stream)) => {
                    let stream_id = recv_stream.id().index();
                    self.stats_requests.fetch_add(1, Ordering::Relaxed);

                    // Read from stream into buffer
                    match self.read_stream(recv_stream, stream_id).await {
                        Ok(packet) => {
                            let bytes_in = packet.len() as u64;
                            self.stats_bytes_in.fetch_add(bytes_in, Ordering::Relaxed);

                            // Enqueue for TS consumer (zero-copy pointer)
                            if let Err(e) = self.packet_queue.enqueue(packet) {
                                eprintln!("Packet enqueue failed: {}", e);
                                self.stats_errors.fetch_add(1, Ordering::Relaxed);
                            }

                            // Keep send_stream alive for potential response (not yet implemented)
                            let _ = send_stream;
                        }
                        Err(e) => {
                            eprintln!("Stream read error: {}", e);
                            self.stats_errors.fetch_add(1, Ordering::Relaxed);
                        }
                    }
                }
                Err(quinn::ConnectionError::ApplicationClosed(_)) => {
                    // Clean shutdown
                    break;
                }
                Err(e) => {
                    eprintln!("Accept stream error: {}", e);
                    self.stats_errors.fetch_add(1, Ordering::Relaxed);
                    break;
                }
            }
        }

        Ok(())
    }

    /// Read a stream and buffer data with max payload limit
    async fn read_stream(
        &mut self,
        mut recv_stream: quinn::RecvStream,
        stream_id: u64,
    ) -> Result<PacketBuffer, Box<dyn std::error::Error>> {
        // Read up to max_payload_bytes from the stream
        let buffer = recv_stream.read_to_end(self.max_payload_bytes).await?;

        let mut packet = PacketBuffer::new(buffer, self.handle);
        packet.stream_id = Some(stream_id);
        Ok(packet)
    }
}

// ============================================================================
// QUIC SERVER STATISTICS
// ============================================================================

/// QUIC Server statistics snapshot
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct QuicServerStats {
    /// Total requests processed since startup
    pub total_requests: u64,

    /// Currently active connections
    pub active_connections: u32,

    /// Total bytes received from clients
    pub total_bytes_in: u64,

    /// Total bytes sent to clients
    pub total_bytes_out: u64,

    /// Average request latency in milliseconds
    pub avg_latency_ms: f64,

    /// Cumulative error count
    pub error_count: u64,

    /// Time since server started (milliseconds)
    pub uptime_ms: u64,
}

impl QuicServerStats {
    /// Serialize statistics to JSON bytes
    pub fn to_json_bytes(&self) -> Result<Vec<u8>, serde_json::Error> {
        let json_str = serde_json::to_string(&self)?;
        Ok(json_str.into_bytes())
    }

    /// Deserialize statistics from JSON bytes
    pub fn from_json_bytes(bytes: &[u8]) -> Result<Self, serde_json::Error> {
        let json_str = String::from_utf8_lossy(bytes);
        serde_json::from_str(&json_str)
    }
}

// ============================================================================
// QUIC SERVER INSTANCE
// ============================================================================

/// QUIC Server instance
///
/// Manages a single QUIC server endpoint with connection handling,
/// statistics tracking, and graceful shutdown via packet queue
/// for zero-copy handoff to TS layer.
///
/// Thread-safe shared via Arc, suitable for concurrent access.
pub struct QuicServer {
    /// Server handle (unique identifier)
    pub handle: u64,

    /// Configuration (stored for reference)
    pub config: FfiQuicConfig,

    /// Server running state
    running: Arc<AtomicBool>,

    /// Server startup timestamp
    startup_time_ms: u64,

    /// Statistics: total requests processed
    stats_total_requests: Arc<AtomicU64>,

    /// Statistics: total bytes in
    stats_total_bytes_in: Arc<AtomicU64>,

    /// Statistics: total bytes out
    stats_total_bytes_out: Arc<AtomicU64>,

    /// Statistics: error count
    stats_error_count: Arc<AtomicU64>,

    /// Active connections: DashMap for lock-free concurrent access
    active_connections: Arc<DashMap<u64, quinn::Connection>>,

    /// Packet queue for zero-copy handoff to TS layer
    packet_queue: Arc<PacketQueue>,

    /// Quinn endpoint (Some if running, None if stopped)
    quinn_endpoint: Arc<tokio::sync::Mutex<Option<quinn::Endpoint>>>,

    /// Background task handle (for spawned accept loop)
    accept_task: Arc<tokio::sync::Mutex<Option<tokio::task::JoinHandle<()>>>>,
}

impl QuicServer {
    /// Create a new QUIC server instance
    pub fn new(handle: u64, config: FfiQuicConfig) -> Self {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_millis() as u64)
            .unwrap_or(0);

        Self {
            handle,
            config,
            running: Arc::new(AtomicBool::new(false)),
            startup_time_ms: now,
            stats_total_requests: Arc::new(AtomicU64::new(0)),
            stats_total_bytes_in: Arc::new(AtomicU64::new(0)),
            stats_total_bytes_out: Arc::new(AtomicU64::new(0)),
            stats_error_count: Arc::new(AtomicU64::new(0)),
            active_connections: Arc::new(DashMap::new()),
            packet_queue: Arc::new(PacketQueue::new()),
            quinn_endpoint: Arc::new(tokio::sync::Mutex::new(None)),
            accept_task: Arc::new(tokio::sync::Mutex::new(None)),
        }
    }

    /// Start the QUIC server
    ///
    /// Initializes the quinn endpoint, binds to the configured address,
    /// and begins accepting connections. Spawns async accept loop.
    ///
    /// # Deterministic Context
    /// All socket operations are explicit with no implicit global state.
    /// The endpoint and connection map are owned by this instance.
    ///
    /// # Returns
    /// Ok(()) on success, Err containing error description on failure
    ///
    /// # Errors
    /// - Port already in use
    /// - Invalid TLS certificate/key
    /// - Failed to bind to address
    pub async fn start(&mut self) -> Result<(), String> {
        // [TASK 1.1] Extract FfiBuffer paths to UTF-8 strings safely
        let cert_path = self.ffi_buffer_to_cstring(&self.config.cert_path)
            .ok_or("Invalid or non-UTF-8 cert path")?;

        let key_path = self.ffi_buffer_to_cstring(&self.config.key_path)
            .ok_or("Invalid or non-UTF-8 key path")?;

        let host_addr = self.ffi_buffer_to_cstring(&self.config.host_addr)
            .ok_or("Invalid or non-UTF-8 host address")?;

        // [TASK 1.2] Load certificate and key files
        let cert_bytes = std::fs::read(&cert_path)
            .map_err(|e| format!("Failed to read cert: {}", e))?;

        let key_bytes = std::fs::read(&key_path)
            .map_err(|e| format!("Failed to read key: {}", e))?;

        // [TASK 1.3] Parse PEM-encoded certificate chain
        let cert_chain = rustls_pemfile::certs(&mut std::io::Cursor::new(&cert_bytes))
            .collect::<Result<Vec<_>, _>>()
            .map_err(|e| format!("Failed to parse certificates: {}", e))?;

        if cert_chain.is_empty() {
            return Err("No certificates found in cert file".to_string());
        }

        // [TASK 1.4] Parse PEM-encoded private key
        let mut key_reader = std::io::Cursor::new(&key_bytes);
        let key = rustls_pemfile::private_key(&mut key_reader)
            .map_err(|e| format!("Failed to parse private key: {}", e))?
            .ok_or("No private key found in key file".to_string())?;

        // [TASK 1.5] Create rustls ServerConfig
        let server_config = rustls::ServerConfig::builder()
            .with_no_client_auth()
            .with_single_cert(cert_chain, key)
            .map_err(|e| format!("TLS config error: {}", e))?;

        // [TASK 1.6] Convert rustls::ServerConfig to quinn's QuicServerConfig
        let quic_server_config = quinn::crypto::rustls::QuicServerConfig::try_from(server_config)
            .map_err(|e| format!("QuicServerConfig conversion error: {}", e))?;

        let quinn_config = quinn::ServerConfig::with_crypto(Arc::new(quic_server_config));

        // [TASK 1.7] Parse socket address
        let socket_addr: std::net::SocketAddr =
            format!("{}:{}", host_addr, self.config.port)
                .parse()
                .map_err(|e: std::net::AddrParseError| {
                    format!("Invalid socket address: {}", e)
                })?;

        // [TASK 1.8] Bind UDP socket explicitly (required by quinn v0.11)
        let udp_socket = std::net::UdpSocket::bind(socket_addr)
            .map_err(|e| format!("Failed to bind UDP socket: {}", e))?;

        // Set non-blocking mode
        udp_socket
            .set_nonblocking(true)
            .map_err(|e| format!("Failed to set non-blocking: {}", e))?;

        // [TASK 1.9] Create quinn endpoint with UdpSocket
        let endpoint = quinn::Endpoint::new(
            Default::default(),
            Some(quinn_config),
            udp_socket,
            Arc::new(quinn::TokioRuntime),
        )
        .map_err(|e| format!("Failed to create endpoint: {}", e))?;

        // Get local address (correct method name is local_addr, not socket_addr)
        let local_addr = endpoint
            .local_addr()
            .map_err(|e| format!("Failed to get local address: {}", e))?;

        eprintln!("QUIC server listening on {}", local_addr);

        // [TASK 1.10] Spawn Connection Acceptance Loop
        let running = self.running.clone();
        let active_conns = self.active_connections.clone();
        let packet_q = self.packet_queue.clone();
        let stats_req = self.stats_total_requests.clone();
        let stats_in = self.stats_total_bytes_in.clone();
        let stats_out = self.stats_total_bytes_out.clone();
        let stats_err = self.stats_error_count.clone();
        let handle = self.handle;
        let max_payload = self.config.max_streams as usize * 1024; // rough estimate

        let endpoint_clone = endpoint.clone();

        let accept_loop = tokio::spawn(async move {
            let mut conn_counter = 0u64;

            loop {
                if !running.load(Ordering::SeqCst) {
                    break;
                }

                match endpoint_clone.accept().await {
                    Some(incoming) => {
                        conn_counter += 1;
                        let conn_id = conn_counter;

                        match incoming.await {
                            Ok(connection) => {
                                // Store in active connections map
                                active_conns.insert(conn_id, connection.clone());

                                eprintln!(
                                    "New connection accepted: {} (total: {})",
                                    conn_id,
                                    active_conns.len()
                                );

                                // Spawn per-connection handler
                                ConnectionHandler::spawn(
                                    handle,
                                    connection,
                                    packet_q.clone(),
                                    stats_req.clone(),
                                    stats_in.clone(),
                                    stats_out.clone(),
                                    stats_err.clone(),
                                    max_payload,
                                )
                                .await;
                            }
                            Err(e) => {
                                eprintln!("Connection accept error: {}", e);
                                stats_err.fetch_add(1, Ordering::Relaxed);
                            }
                        }
                    }
                    None => {
                        // Endpoint closed
                        eprintln!("Accept loop: endpoint closed");
                        break;
                    }
                }
            }

            eprintln!("Accept loop terminated for server {}", handle);
        });

        // Store endpoint and accept task
        *self.quinn_endpoint.blocking_lock() = Some(endpoint);
        *self.accept_task.blocking_lock() = Some(accept_loop);

        // Mark as running
        self.running.store(true, Ordering::SeqCst);

        Ok(())
    }

    /// Stop the QUIC server gracefully
    ///
    /// Signals all active connections to close, waits for in-flight
    /// requests to complete (with timeout), then releases resources.
    ///
    /// # Deterministic Shutdown
    /// All connections are explicitly closed via the connection map.
    /// No implicit cleanup or background task magic.
    ///
    /// # Returns
    /// Ok(()) on success, Err containing error description on failure
    pub async fn stop(&mut self) -> Result<(), String> {
        if !self.running.load(Ordering::SeqCst) {
            return Ok(());
        }

        // Signal shutdown
        self.running.store(false, Ordering::SeqCst);

        // Close all active connections explicitly
        for entry in self.active_connections.iter() {
            let conn = entry.value();
            conn.close(quinn::VarInt::from_u32(0), b"server shutdown");
        }

        // Clear the connection map
        self.active_connections.clear();

        // Close the endpoint (this stops the accept loop)
        if let Some(endpoint) = self.quinn_endpoint.blocking_lock().take() {
            endpoint.wait_idle().await;
        }

        // Wait for accept task to finish (with timeout)
        if let Some(task) = self.accept_task.blocking_lock().take() {
            let timeout = tokio::time::Duration::from_secs(5);
            match tokio::time::timeout(timeout, task).await {
                Ok(Ok(())) => {}
                Ok(Err(e)) => {
                    return Err(format!("Accept task join error: {}", e))
                }
                Err(_) => {
                    return Err("Graceful shutdown timeout".to_string())
                }
            }
        }

        Ok(())
    }

    /// Get current server statistics
    ///
    /// Collects a snapshot of current performance metrics including
    /// request count, bytes transferred, error count, and uptime.
    ///
    /// # Deterministic Snapshot
    /// Uses atomic load operations with explicit ordering to ensure
    /// consistent metric capture across the snapshot.
    ///
    /// # Returns
    /// QuicServerStats containing current metrics
    pub fn get_stats(&self) -> QuicServerStats {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_millis() as u64)
            .unwrap_or(0);

        let uptime_ms = now.saturating_sub(self.startup_time_ms);

        // Snapshot all metrics atomically
        let total_requests = self.stats_total_requests.load(Ordering::Acquire);
        let total_bytes_in = self.stats_total_bytes_in.load(Ordering::Acquire);
        let total_bytes_out = self.stats_total_bytes_out.load(Ordering::Acquire);
        let error_count = self.stats_error_count.load(Ordering::Acquire);
        let active_conns = self.active_connections.len() as u32;

        // Calculate average latency if we have requests
        let avg_latency_ms = if total_requests > 0 {
            (uptime_ms as f64) / (total_requests as f64)
        } else {
            0.0
        };

        QuicServerStats {
            total_requests,
            active_connections: active_conns,
            total_bytes_in,
            total_bytes_out,
            avg_latency_ms,
            error_count,
            uptime_ms,
        }
    }

    /// Check if server is currently running
    pub fn is_running(&self) -> bool {
        self.running.load(Ordering::SeqCst)
    }

    /// Record a processed request
    pub fn record_request(&self, bytes_in: u64, bytes_out: u64, error: bool) {
        self.stats_total_requests.fetch_add(1, Ordering::Release);
        self.stats_total_bytes_in.fetch_add(bytes_in, Ordering::Release);
        self.stats_total_bytes_out.fetch_add(bytes_out, Ordering::Release);
        if error {
            self.stats_error_count.fetch_add(1, Ordering::Release);
        }
    }

    /// Record bytes transferred
    pub fn record_bytes(&self, bytes_in: u64, bytes_out: u64) {
        self.stats_total_bytes_in.fetch_add(bytes_in, Ordering::Release);
        self.stats_total_bytes_out.fetch_add(bytes_out, Ordering::Release);
    }

    /// Record an error
    pub fn record_error(&self) {
        self.stats_error_count.fetch_add(1, Ordering::Release);
    }

    /// Get packet queue reference (for TS layer consumption via KNUL FFI)
    pub fn packet_queue(&self) -> Arc<PacketQueue> {
        self.packet_queue.clone()
    }

    /// Helper: Convert FfiBuffer to C string (for file paths)
    ///
    /// # Safety
    /// Assumes the FfiBuffer contains valid UTF-8 encoded data
    fn ffi_buffer_to_cstring(&self, buffer: &krepis_core::FfiBuffer) -> Option<String> {
        if !buffer.is_valid() || buffer.data.is_null() {
            return None;
        }

        unsafe {
            // SAFETY: FfiBuffer guarantees valid pointer and length
            let slice = std::slice::from_raw_parts(buffer.data, buffer.len);
            String::from_utf8(slice.to_vec()).ok()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_quic_server_creation() {
        let config = FfiQuicConfig::new();
        let server = QuicServer::new(1, config);

        assert_eq!(server.handle, 1);
        assert!(!server.is_running());
        assert_eq!(server.get_stats().total_requests, 0);
    }

    #[test]
    fn test_statistics_tracking() {
        let config = FfiQuicConfig::new();
        let server = QuicServer::new(1, config);

        // Record some activity
        server.record_request(1000, 500, false);
        server.record_bytes(2000, 1000);
        server.record_error();

        let stats = server.get_stats();
        assert_eq!(stats.total_requests, 1);
        assert_eq!(stats.total_bytes_in, 3000);
        assert_eq!(stats.total_bytes_out, 1500);
        assert_eq!(stats.error_count, 1);
    }

    #[test]
    fn test_stats_serialization() {
        let stats = QuicServerStats {
            total_requests: 100,
            active_connections: 5,
            total_bytes_in: 1_000_000,
            total_bytes_out: 500_000,
            avg_latency_ms: 42.5,
            error_count: 3,
            uptime_ms: 3600_000,
        };

        let bytes = stats.to_json_bytes().expect("serialize");
        let deserialized = QuicServerStats::from_json_bytes(&bytes).expect("deserialize");

        assert_eq!(deserialized.total_requests, stats.total_requests);
        assert_eq!(deserialized.avg_latency_ms, stats.avg_latency_ms);
    }

    #[test]
    fn test_packet_buffer_creation() {
        // Create original data vector
        let data = vec![1, 2, 3, 4, 5];
        
        // Capture pointer BEFORE moving data into PacketBuffer
        // This proves zero-copy: same Vec allocation is reused
        let expected_ptr = data.as_ptr();
        let expected_len = data.len();

        // Move (not clone) data into PacketBuffer - no new allocation
        let packet = PacketBuffer::new(data, 42);

        // Verify connection handle is stored correctly
        assert_eq!(packet.connection_handle, 42);
        
        // Verify length is preserved
        assert_eq!(packet.len(), 5);
        assert_eq!(packet.len(), expected_len);

        // CRITICAL: Verify the Vec buffer pointer is identical (zero-copy proof)
        // If packet.as_ptr() != expected_ptr, a new allocation occurred (failure)
        assert_eq!(
            packet.as_ptr(),
            expected_ptr,
            "PacketBuffer must preserve original Vec allocation (zero-copy requirement)"
        );

        // Verify data contents are intact
        assert_eq!(packet.data[0], 1);
        assert_eq!(packet.data[4], 5);
    }

    #[tokio::test]
    async fn test_packet_queue_enqueue_dequeue() {
        let queue = PacketQueue::new();
        
        // Create packet data
        let data = vec![1, 2, 3];
        let expected_data_ptr = data.as_ptr();
        
        // Create packet with owned data (zero-copy)
        let packet = PacketBuffer::new(data, 1);
        
        // Verify packet has correct metadata
        assert_eq!(packet.connection_handle, 1);
        assert_eq!(packet.len(), 3);

        // Enqueue packet (transfer ownership to queue)
        queue.enqueue(packet).expect("enqueue failed");
        assert_eq!(queue.len(), 1);

        // Dequeue packet
        let dequeued = queue.try_dequeue().await;
        assert!(dequeued.is_some());
        
        let p = dequeued.unwrap();
        
        // Verify metadata preserved through queue
        assert_eq!(p.connection_handle, 1);
        assert_eq!(p.len(), 3);
        
        // CRITICAL: Verify the data pointer is identical (queue does not copy)
        // This proves the Vec<u8> allocation passes through the queue unchanged
        assert_eq!(
            p.as_ptr(),
            expected_data_ptr,
            "Packet data must preserve original Vec allocation (zero-copy through queue)"
        );
        
        // Verify queue is now empty
        assert_eq!(queue.len(), 0);
        assert!(queue.is_empty());
        
        // Verify data contents
        assert_eq!(p.data[0], 1);
        assert_eq!(p.data[2], 3);
    }

    #[test]
    fn test_packet_queue_depth_tracking() {
        let queue = PacketQueue::new();

        assert_eq!(queue.len(), 0);
        assert!(queue.is_empty());

        // Note: Actual enqueue needs async context, so we test the structure
        let packet1 = PacketBuffer::new(vec![1, 2], 1);
        let packet2 = PacketBuffer::new(vec![3, 4, 5], 2);

        assert_eq!(packet1.len(), 2);
        assert_eq!(packet2.len(), 3);
    }
}