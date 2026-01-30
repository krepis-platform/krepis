//! Transport Domain
//!
//! Abstract network transport interface that decouples the Krepis kernel from
//! concrete implementations (QUIC, HTTP/3, etc.). Enables testing, protocol
//! flexibility, and version independence.
//!
//! ## Design Rationale (Project Clear-Link v2.0)
//!
//! The `SovereignTransport` trait establishes a clear boundary between the Krepis kernel's
//! high-level protocol requirements and concrete transport implementations (QUIC, HTTP/3, etc.).
//! This design principle—"Abstraction Barrier"—allows:
//!
//! - **Implementation Flexibility**: Swap transport backends without kernel changes
//! - **Testing Isolation**: Mock implementations for unit tests and formal verification
//! - **Version Decoupling**: Kernel remains independent of quinn/rustls version constraints
//! - **Deterministic Context**: All transport operations are explicit and traceable
//!
//! ## Architectural Principles
//!
//! 1. **Fractal Integrity**: Each transport handles only network I/O; no business logic
//! 2. **Native-First**: Rust's type system enforces safety and thread-safety bounds
//! 3. **Zero-Copy Semantics**: Packet data flows by reference; metadata by value
//! 4. **Error Consistency**: All error paths map to `KrepisError` for unified handling

use async_trait::async_trait;
use crate::domain::KrepisError;
use crate::infrastructure::abi::FfiQuicConfig;
use std::fmt;

/// Unique identifier for a transport server instance
/// Opaque 64-bit handle managed by the transport implementation
pub type TransportHandle = u64;

/// Packet metadata and zero-copy buffer reference
///
/// Produced by the transport layer and consumed by the kernel.
/// The contained buffer remains valid only while pinned in the queue.
#[derive(Debug, Clone)]
pub struct TransportPacket {
    /// Raw packet bytes (pointer owned by transport, pinned in queue)
    pub data: Vec<u8>,
    
    /// Source connection identifier (connection-scoped within this server)
    pub connection_id: u64,
    
    /// Timestamp of packet receipt (microseconds since Unix epoch)
    pub timestamp_us: u64,
    
    /// Protocol-specific stream identifier (optional, transport-dependent)
    pub stream_id: Option<u64>,
}

impl TransportPacket {
    /// Create a new transport packet with current timestamp
    pub fn new(data: Vec<u8>, connection_id: u64) -> Self {
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_micros() as u64)
            .unwrap_or(0);

        Self {
            data,
            connection_id,
            timestamp_us: now,
            stream_id: None,
        }
    }

    /// Byte length of packet data
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Check if packet is empty
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// Pointer to packet data (for FFI and Deno memory view compatibility)
    pub fn as_ptr(&self) -> *const u8 {
        self.data.as_ptr()
    }
}

/// Transport layer statistics snapshot
///
/// Provides real-time metrics for monitoring and resource decision-making.
/// All counters are atomic snapshots—no blocking or coordination required.
#[derive(Debug, Clone, Default)]
pub struct TransportStats {
    /// Total incoming packets processed since server start
    pub total_packets_received: u64,
    
    /// Currently active client connections
    pub active_connections: u32,
    
    /// Total bytes ingress (client → server)
    pub total_bytes_in: u64,
    
    /// Total bytes egress (server → client)
    pub total_bytes_out: u64,
    
    /// Cumulative protocol errors (malformed packets, timeout, etc.)
    pub error_count: u64,
    
    /// Server uptime in milliseconds
    pub uptime_ms: u64,
    
    /// Average latency per packet in milliseconds (uptime / packets)
    pub avg_latency_ms: f64,
}

/// Core abstraction for network transport implementations
///
/// This trait defines the contract between the Krepis kernel (consumer) and
/// transport implementations (providers). It enforces:
///
/// - **Thread Safety**: Implementations must be `Send + Sync` for concurrent access
/// - **Error Consistency**: All errors map to `KrepisError` for kernel unification
/// - **Deterministic Lifecycle**: Explicit start/stop with clear state transitions
/// - **Zero-Copy I/O**: Packets move by ownership, never copied within transport
///
/// # Lifetime and Handle Semantics
///
/// Each transport instance is created with `start()`, returning a handle. The handle
/// remains valid until `stop()` is called. After stopping, the handle is invalid and
/// must not be reused. Multiple handles can coexist (multiple server instances).
///
/// # Async Safety
///
/// All methods are async to support the tokio runtime. Implementations must not block
/// or perform CPU-intensive work; I/O operations should use async/await.
///
/// # Error Propagation
///
/// All errors must be converted to `KrepisError` variants for uniform kernel error
/// handling. Transport-specific errors should be mapped to the most appropriate
/// `KrepisError` category (e.g., `NetworkError`, `QuotaExceeded`, `Timeout`).
#[async_trait]
pub trait SovereignTransport: Send + Sync + fmt::Debug {
    /// Start a transport server instance
    ///
    /// Initializes and binds a server socket, configures TLS/crypto, and begins
    /// accepting incoming client connections. This is a resource allocation point;
    /// failure to stop the server will leak resources.
    ///
    /// # Arguments
    ///
    /// - `config`: Transport configuration (address, port, TLS paths, limits)
    ///
    /// # Returns
    ///
    /// On success, returns an opaque `TransportHandle` (u64) that identifies this
    /// server instance. This handle is used for all subsequent operations on this server.
    ///
    /// # Errors
    ///
    /// - `NetworkError`: Failed to bind to port or socket configuration error
    /// - `InvalidRequest`: Configuration is invalid (port=0, missing TLS certs, etc.)
    /// - `Internal`: Unexpected error (panic recovery, unrecoverable state)
    ///
    /// # Concurrency
    ///
    /// Multiple `start()` calls may be active simultaneously; each produces a
    /// distinct handle. The implementation must manage per-instance state safely.
    async fn start(&self, config: FfiQuicConfig) -> Result<TransportHandle, KrepisError>;

    /// Stop a running transport server instance
    ///
    /// Gracefully closes all client connections, drains pending packets, and releases
    /// all socket and memory resources associated with this server. After this call,
    /// the handle is invalid.
    ///
    /// # Arguments
    ///
    /// - `handle`: Server instance identifier (from `start()`)
    ///
    /// # Returns
    ///
    /// `Ok(())` on successful shutdown, or `KrepisError` on failure.
    ///
    /// # Errors
    ///
    /// - `InvalidPointer`: Handle not found (already stopped or never existed)
    /// - `Timeout`: Graceful shutdown exceeded time limit (some resources may leak)
    /// - `Internal`: Unexpected error during shutdown
    ///
    /// # Concurrency
    ///
    /// Safe to call while `dequeue_packet()` or `get_stats()` are running on other tasks.
    /// Ongoing operations may receive errors as the server shuts down.
    async fn stop(&self, handle: TransportHandle) -> Result<(), KrepisError>;

    /// Dequeue the next received packet from a server instance
    ///
    /// Non-blocking attempt to retrieve a packet from the transport's inbound queue.
    /// Returns immediately whether or not a packet is available. This method is
    /// designed for polling patterns or integration with kernel scheduler loops.
    ///
    /// # Arguments
    ///
    /// - `handle`: Server instance identifier
    ///
    /// # Returns
    ///
    /// - `Ok(Some(packet))`: Packet available; caller owns the packet data
    /// - `Ok(None)`: No packets available (queue empty, not an error)
    /// - `Err(error)`: Server error prevents dequeueing (server stopped, etc.)
    ///
    /// # Errors
    ///
    /// - `InvalidPointer`: Handle not found or server is stopped
    /// - `Internal`: Unexpected queue error
    ///
    /// # Zero-Copy Guarantee
    ///
    /// The returned `TransportPacket.data` (Vec<u8>) is never copied within the
    /// transport layer. The allocation from the network receive path transfers
    /// directly to the caller. Deno can construct a memory view over this buffer
    /// without additional allocation.
    ///
    /// # Concurrency
    ///
    /// Multiple tasks may call `dequeue_packet()` on the same handle. The implementation
    /// must ensure packets are distributed fairly (FIFO) and no packets are lost.
    async fn dequeue_packet(
        &self,
        handle: TransportHandle,
    ) -> Result<Option<TransportPacket>, KrepisError>;

    /// Retrieve current statistics for a server instance
    ///
    /// Returns a snapshot of performance metrics without blocking. All counter values
    /// are atomic reads; no synchronization or state copying occurs.
    ///
    /// # Arguments
    ///
    /// - `handle`: Server instance identifier
    ///
    /// # Returns
    ///
    /// `Ok(stats)` with current metrics, or `KrepisError` if the handle is invalid.
    ///
    /// # Errors
    ///
    /// - `InvalidPointer`: Handle not found
    /// - `Internal`: Unexpected error reading metrics
    ///
    /// # Consistency
    ///
    /// The stats snapshot may reflect partially committed updates. For example,
    /// `total_packets_received` might increment between reading two other fields.
    /// The snapshot is not transactional, but each individual counter value is
    /// atomically read at the moment of access.
    async fn get_stats(&self, handle: TransportHandle) -> Result<TransportStats, KrepisError>;

    /// Enqueue a packet for transmission to a specific client connection
    ///
    /// Asynchronously queues a packet for transmission without blocking on network I/O.
    /// The packet is enqueued and the method returns immediately; actual transmission
    /// happens on the transport's background sender task.
    ///
    /// ## Design Principles
    ///
    /// **Asynchronous Sending**: Network I/O is decoupled from the caller. The kernel
    /// can submit packets for sending without waiting for socket readiness or transmission
    /// completion. This maintains the non-blocking, deterministic execution model.
    ///
    /// **Target Specification**: The `connection_id` field in the packet identifies the
    /// specific client connection that should receive the data. This enables the transport
    /// to route packets to the correct recipient without additional routing tables.
    ///
    /// **Zero-Copy Transmission**: Ownership of the packet data (Vec<u8>) transfers
    /// directly from the kernel to the transport layer. The transport never copies data;
    /// the allocation flows unchanged to the hardware/network interface. This minimizes
    /// memory pressure and GC overhead during high-throughput scenarios.
    ///
    /// # Arguments
    ///
    /// - `handle`: Server instance identifier (from `start()`)
    /// - `packet`: Packet to send, with `connection_id` specifying the recipient
    ///
    /// # Returns
    ///
    /// - `Ok(())`: Packet successfully enqueued for transmission
    /// - `Err(KrepisError)`: Enqueueing failed
    ///
    /// # Errors
    ///
    /// - `InvalidPointer`: Handle not found or server is stopped
    /// - `QuotaExceeded`: Send queue is full (backpressure limit reached)
    /// - `Internal`: Unexpected error during enqueue
    ///
    /// # Note on Delivery
    ///
    /// This method does NOT guarantee delivery. The packet is queued, but may be:
    /// - Lost if the connection closes before transmission
    /// - Dropped if the send queue overflows (backpressure)
    /// - Delayed arbitrarily (no latency guarantees)
    ///
    /// The kernel is responsible for implementing retransmission logic if guaranteed
    /// delivery is required.
    ///
    /// # Backpressure Handling
    ///
    /// When the send queue reaches its limit, this method returns `QuotaExceeded`.
    /// The kernel should respect this signal and either:
    /// - Backoff and retry later
    /// - Implement its own queue management upstream
    /// - Close the connection if backpressure persists
    async fn enqueue_send_packet(
        &self,
        handle: TransportHandle,
        packet: TransportPacket,
    ) -> Result<(), KrepisError>;

    /// Optional: Query if a server instance is currently running
    ///
    /// Allows the kernel to determine if a handle is valid without attempting
    /// an operation. Default implementation returns `true` (assume running).
    async fn is_running(&self, _handle: TransportHandle) -> bool {
        // Optimistic assumption; implementations can override for precise checks
        true
    }
}

/// Factory trait for creating SovereignTransport instances
///
/// Enables dynamic transport selection at runtime. The kernel uses this to
/// instantiate the configured transport backend.
pub trait TransportFactory: Send + Sync {
    /// Create a new SovereignTransport instance
    fn create(&self) -> Box<dyn SovereignTransport>;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn transport_packet_creation() {
        let data = vec![1, 2, 3, 4, 5];
        let ptr_before = data.as_ptr();
        let packet = TransportPacket::new(data, 42);

        assert_eq!(packet.connection_id, 42);
        assert_eq!(packet.len(), 5);
        assert_eq!(packet.as_ptr(), ptr_before);
        assert!(!packet.is_empty());
    }

    #[test]
    fn transport_stats_default() {
        let stats = TransportStats::default();

        assert_eq!(stats.total_packets_received, 0);
        assert_eq!(stats.active_connections, 0);
        assert_eq!(stats.error_count, 0);
    }

    #[test]
    fn transport_handle_is_u64() {
        let handle: TransportHandle = 12345u64;
        assert_eq!(handle, 12345);
    }
}