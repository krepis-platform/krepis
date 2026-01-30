//! QUIC Connection Handler
//!
//! Per-connection task that accepts bidirectional streams from QUIC clients
//! and routes incoming data to the packet queue for kernel processing.

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

use crate::domain::types::PacketBuffer;
use crate::infrastructure::queue::PacketQueue;

/// Per-connection handler task spawned when accepting a new connection
///
/// Each connection spawns its own handler task that reads from streams
/// and enqueues packets for processing.
pub struct ConnectionHandler {
    handle: u64,
    connection: quinn::Connection,
    packet_queue: Arc<PacketQueue>,
    stats_requests: Arc<AtomicU64>,
    stats_bytes_in: Arc<AtomicU64>,
    _stats_bytes_out: Arc<AtomicU64>,
    stats_errors: Arc<AtomicU64>,
    max_payload_bytes: usize,
}

impl ConnectionHandler {
    /// Spawn a new connection handler task
    pub async fn spawn(
        handle: u64,
        connection: quinn::Connection,
        packet_queue: Arc<PacketQueue>,
        stats_requests: Arc<AtomicU64>,
        stats_bytes_in: Arc<AtomicU64>,
        _stats_bytes_out: Arc<AtomicU64>,
        stats_errors: Arc<AtomicU64>,
        max_payload_bytes: usize,
    ) {
        let handler = Self {
            handle,
            connection,
            packet_queue,
            stats_requests,
            stats_bytes_in,
            _stats_bytes_out,
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

                    match self.read_stream(recv_stream, stream_id).await {
                        Ok(packet) => {
                            let bytes_in = packet.len() as u64;
                            self.stats_bytes_in.fetch_add(bytes_in, Ordering::Relaxed);

                            if let Err(e) = self.packet_queue.enqueue(packet) {
                                eprintln!("Packet enqueue failed: {}", e);
                                self.stats_errors.fetch_add(1, Ordering::Relaxed);
                            }

                            let _ = send_stream;
                        }
                        Err(e) => {
                            eprintln!("Stream read error: {}", e);
                            self.stats_errors.fetch_add(1, Ordering::Relaxed);
                        }
                    }
                }
                Err(quinn::ConnectionError::ApplicationClosed(_)) => {
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
        let buffer = recv_stream.read_to_end(self.max_payload_bytes).await?;

        let mut packet = PacketBuffer::new(buffer, self.handle);
        packet.stream_id = Some(stream_id);
        Ok(packet)
    }
}