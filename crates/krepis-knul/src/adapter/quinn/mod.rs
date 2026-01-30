//! Quinn Transport Adapter
//!
//! Complete Quinn-based QUIC transport implementation of the SovereignTransport
//! trait. Wraps quinn-specific logic and provides clean abstraction boundary.

pub mod handler;
pub mod server;

use async_trait::async_trait;
use dashmap::DashMap;
use krepis_core::domain::transport::{SovereignTransport, TransportHandle, TransportPacket, TransportStats};
use krepis_core::KrepisError;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

use krepis_core::FfiQuicConfig;
pub use server::QuicServer;

/// Quinn-based transport implementation of SovereignTransport
///
/// This structure wraps the quinn-specific implementation details and provides
/// a clean abstraction boundary that allows the kernel to interact with transport
/// without depending on quinn, rustls, or other version-specific dependencies.
#[derive(Debug)]
pub struct QuinnTransport {
    /// Internal server registry for managing multiple instances
    servers: Arc<DashMap<TransportHandle, Arc<QuicServer>>>,
    /// Handle allocator for generating unique server identifiers
    next_handle: Arc<AtomicU64>,
}

impl QuinnTransport {
    /// Create a new Quinn transport factory
    pub fn new() -> Self {
        Self {
            servers: Arc::new(DashMap::new()),
            next_handle: Arc::new(AtomicU64::new(1)),
        }
    }

    /// Allocate the next unique handle
    fn allocate_handle(&self) -> TransportHandle {
        self.next_handle.fetch_add(1, Ordering::SeqCst)
    }

    /// Get reference to a registered server
    fn get_server(&self, handle: TransportHandle) -> Option<Arc<QuicServer>> {
        self.servers.get(&handle).map(|entry| Arc::clone(&entry))
    }
}

impl Default for QuinnTransport {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait]
impl SovereignTransport for QuinnTransport {
    async fn start(&self, config: FfiQuicConfig) -> Result<TransportHandle, KrepisError> {
        let handle = self.allocate_handle();
        let server = QuicServer::new(handle, config);

        server.start().await?;

        self.servers.insert(handle, Arc::new(server));

        Ok(handle)
    }

    async fn stop(&self, handle: TransportHandle) -> Result<(), KrepisError> {
        let server = self
            .servers
            .remove(&handle)
            .map(|(_, s)| s)
            .ok_or(KrepisError::InvalidPointer)?;

        server.stop().await?;

        Ok(())
    }

    async fn dequeue_packet(
        &self,
        handle: TransportHandle,
    ) -> Result<Option<TransportPacket>, KrepisError> {
        let server = self
            .get_server(handle)
            .ok_or(KrepisError::InvalidPointer)?;

        let packet = server
            .packet_queue()
            .try_dequeue()
            .await
            .map(|pb| pb.into_transport_packet());

        Ok(packet)
    }

    async fn get_stats(&self, handle: TransportHandle) -> Result<TransportStats, KrepisError> {
        let server = self
            .get_server(handle)
            .ok_or(KrepisError::InvalidPointer)?;

        let stats = server.get_stats().into_transport_stats();

        Ok(stats)
    }

    async fn enqueue_send_packet(
        &self,
        handle: TransportHandle,
        packet: TransportPacket,
    ) -> Result<(), KrepisError> {
        let server = self
            .get_server(handle)
            .ok_or(KrepisError::InvalidPointer)?;

        server.send_packet(packet).await
    }

    async fn is_running(&self, handle: TransportHandle) -> bool {
        self.get_server(handle)
            .map(|server| server.is_running())
            .unwrap_or(false)
    }
}