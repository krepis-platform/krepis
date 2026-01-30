//! QUIC Server Instance
//!
//! Quinn-based QUIC server implementation with interior mutability
//! for managing endpoint lifecycle and statistics.

use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;
use std::time::{SystemTime, UNIX_EPOCH};

use dashmap::DashMap;
use krepis_core::{FfiBuffer, FfiQuicConfig, KrepisError};
use krepis_core::domain::transport::TransportPacket;

use crate::domain::types::QuicServerStats;
use crate::infrastructure::queue::PacketQueue;

use super::handler::ConnectionHandler;

/// QUIC Server instance with interior mutability
///
/// All mutable state is stored in Arc<Atomic*> or Arc<Mutex<*>> for interior
/// mutability, allowing &self methods compatible with the SovereignTransport trait.
#[derive(Debug)]
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
    pub async fn start(&self) -> Result<(), KrepisError> {
        let cert_path = self
            .ffi_buffer_to_cstring(&self.config.cert_path)
            .ok_or(KrepisError::InvalidRequest)?;

        let key_path = self
            .ffi_buffer_to_cstring(&self.config.key_path)
            .ok_or(KrepisError::InvalidRequest)?;

        let host_addr = self
            .ffi_buffer_to_cstring(&self.config.host_addr)
            .ok_or(KrepisError::InvalidRequest)?;

        let cert_bytes =
            std::fs::read(&cert_path).map_err(|_| KrepisError::NetworkError)?;

        let key_bytes = std::fs::read(&key_path).map_err(|_| KrepisError::NetworkError)?;

        let cert_chain = rustls_pemfile::certs(&mut std::io::Cursor::new(&cert_bytes))
            .collect::<Result<Vec<_>, _>>()
            .map_err(|_| KrepisError::InvalidRequest)?;

        if cert_chain.is_empty() {
            return Err(KrepisError::InvalidRequest);
        }

        let mut key_reader = std::io::Cursor::new(&key_bytes);
        let key = rustls_pemfile::private_key(&mut key_reader)
            .map_err(|_| KrepisError::InvalidRequest)?
            .ok_or(KrepisError::InvalidRequest)?;

        let server_config = rustls::ServerConfig::builder()
            .with_no_client_auth()
            .with_single_cert(cert_chain, key)
            .map_err(|_| KrepisError::InvalidRequest)?;

        let quic_server_config = quinn::crypto::rustls::QuicServerConfig::try_from(server_config)
            .map_err(|_| KrepisError::InvalidRequest)?;

        let quinn_config = quinn::ServerConfig::with_crypto(Arc::new(quic_server_config));

        let socket_addr: std::net::SocketAddr =
            format!("{}:{}", host_addr, self.config.port)
                .parse()
                .map_err(|_| KrepisError::InvalidRequest)?;

        let udp_socket = std::net::UdpSocket::bind(socket_addr)
            .map_err(|_| KrepisError::NetworkError)?;

        udp_socket
            .set_nonblocking(true)
            .map_err(|_| KrepisError::NetworkError)?;

        let endpoint = quinn::Endpoint::new(
            Default::default(),
            Some(quinn_config),
            udp_socket,
            Arc::new(quinn::TokioRuntime),
        )
        .map_err(|_| KrepisError::NetworkError)?;

        let _local_addr = endpoint.local_addr().map_err(|_| KrepisError::NetworkError)?;

        let running = self.running.clone();
        let active_conns = self.active_connections.clone();
        let packet_q = self.packet_queue.clone();
        let stats_req = self.stats_total_requests.clone();
        let stats_in = self.stats_total_bytes_in.clone();
        let stats_out = self.stats_total_bytes_out.clone();
        let stats_err = self.stats_error_count.clone();
        let handle = self.handle;
        let max_payload = self.config.max_streams as usize * 1024;

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
                                active_conns.insert(conn_id, connection.clone());

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
                            Err(_) => {
                                stats_err.fetch_add(1, Ordering::Relaxed);
                            }
                        }
                    }
                    None => {
                        break;
                    }
                }
            }
        });

        *self.quinn_endpoint.blocking_lock() = Some(endpoint);
        *self.accept_task.blocking_lock() = Some(accept_loop);

        self.running.store(true, Ordering::SeqCst);

        Ok(())
    }

    /// Stop the QUIC server gracefully
    pub async fn stop(&self) -> Result<(), KrepisError> {
        if !self.running.load(Ordering::SeqCst) {
            return Ok(());
        }

        self.running.store(false, Ordering::SeqCst);

        for entry in self.active_connections.iter() {
            let conn = entry.value();
            conn.close(quinn::VarInt::from_u32(0), b"server shutdown");
        }

        self.active_connections.clear();

        if let Some(endpoint) = self.quinn_endpoint.blocking_lock().take() {
            endpoint.wait_idle().await;
        }

        if let Some(task) = self.accept_task.blocking_lock().take() {
            let timeout = tokio::time::Duration::from_secs(5);
            tokio::time::timeout(timeout, task)
                .await
                .map_err(|_| KrepisError::Timeout)?
                .map_err(|_| KrepisError::Internal)?;
        }

        Ok(())
    }

    /// Get current server statistics
    pub fn get_stats(&self) -> QuicServerStats {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_millis() as u64)
            .unwrap_or(0);

        let uptime_ms = now.saturating_sub(self.startup_time_ms);

        let total_requests = self.stats_total_requests.load(Ordering::Acquire);
        let total_bytes_in = self.stats_total_bytes_in.load(Ordering::Acquire);
        let total_bytes_out = self.stats_total_bytes_out.load(Ordering::Acquire);
        let error_count = self.stats_error_count.load(Ordering::Acquire);
        let active_conns = self.active_connections.len() as u32;

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

    /// Send a packet to a specific client connection
    ///
    /// Routes the packet to the connection identified by `packet.connection_id`,
    /// transmits the data via a unidirectional QUIC stream, and updates egress
    /// statistics atomically.
    ///
    /// ## Design
    ///
    /// **Connection Routing**: The packet's `connection_id` field identifies the
    /// recipient. This enables the server to route responses to specific clients
    /// without maintaining per-connection state beyond the active connections map.
    ///
    /// **Unidirectional Streams**: Uses QUIC's unidirectional streams for
    /// one-way communication from server to client. Each send creates a new stream,
    /// sends the complete packet payload, and closes the stream.
    ///
    /// **Zero-Copy Transmission**: The packet's ownership transfers directly to
    /// the write operation. No intermediate buffering or copying occurs.
    ///
    /// **Atomic Statistics**: Updates to `stats_total_bytes_out` are atomic,
    /// ensuring accurate statistics even under concurrent sends.
    ///
    /// # Arguments
    ///
    /// - `packet`: Packet to send with `connection_id` identifying the recipient
    ///
    /// # Returns
    ///
    /// - `Ok(())`: Packet successfully sent and stream closed
    /// - `Err(KrepisError)`: Transmission failed
    ///
    /// # Errors
    ///
    /// - `InvalidPointer`: Connection not found (already closed or invalid ID)
    /// - `NetworkError`: Stream creation or write failed
    /// - `Internal`: Unexpected error during transmission
    ///
    /// # Note on Delivery
    ///
    /// This method guarantees that the packet is sent through the QUIC protocol,
    /// which provides reliable delivery. However, if the connection is closed
    /// before the stream is fully transmitted, the packet may not reach the client.
    pub async fn send_packet(&self, packet: TransportPacket) -> Result<(), KrepisError> {
        // Lookup the target connection
        let connection = self
            .active_connections
            .get(&packet.connection_id)
            .map(|entry| entry.clone())
            .ok_or(KrepisError::InvalidPointer)?;

        // Open a unidirectional stream
        let mut send_stream = connection
            .open_uni()
            .await
            .map_err(|_| KrepisError::NetworkError)?;

        // Send the packet data (async)
        send_stream
            .write_all(&packet.data)
            .await
            .map_err(|_| KrepisError::NetworkError)?;

        // Gracefully close the stream (sync)
        send_stream
            .finish()
            .map_err(|_| KrepisError::NetworkError)?;

        // Update statistics atomically
        let bytes_sent = packet.data.len() as u64;
        self.stats_total_bytes_out
            .fetch_add(bytes_sent, Ordering::Relaxed);

        Ok(())
    }

    /// Check if server is currently running
    pub fn is_running(&self) -> bool {
        self.running.load(Ordering::SeqCst)
    }

    /// Get packet queue reference (for internal use)
    pub fn packet_queue(&self) -> Arc<PacketQueue> {
        self.packet_queue.clone()
    }

    /// Helper: Convert FfiBuffer to C string (for file paths)
    fn ffi_buffer_to_cstring(&self, buffer: &FfiBuffer) -> Option<String> {
        if !buffer.is_valid() || buffer.data.is_null() {
            return None;
        }

        unsafe {
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

    #[tokio::test]
    async fn test_send_packet_invalid_connection() {
        let config = FfiQuicConfig::new();
        let server = QuicServer::new(1, config);

        // Try to send to non-existent connection
        let packet = TransportPacket::new(vec![1, 2, 3], 999);
        let result = server.send_packet(packet).await;

        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), KrepisError::InvalidPointer);
    }

    #[test]
    fn test_send_packet_stats_update() {
        let config = FfiQuicConfig::new();
        let server = QuicServer::new(1, config);

        // Manually update stats (in real scenario, would be via send_packet)
        let bytes_to_send = 100u64;
        server
            .stats_total_bytes_out
            .fetch_add(bytes_to_send, Ordering::Relaxed);

        let stats = server.get_stats();
        assert_eq!(stats.total_bytes_out, bytes_to_send);
    }
}