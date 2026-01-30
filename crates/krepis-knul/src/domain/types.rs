//! Domain Types Module
//!
//! Core domain data structures for packet handling and statistics.
//! Includes trait conversions for bridging to krepis-core abstractions.

use krepis_core::domain::transport::{TransportPacket, TransportStats};
use serde::{Deserialize, Serialize};
use std::time::{SystemTime, UNIX_EPOCH};

/// Internal packet representation before conversion to TransportPacket
///
/// This maintains zero-copy semantics during queue transit by preserving
/// the original Vec<u8> allocation from the network receive path.
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
    /// Create a new packet buffer with current timestamp
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

    /// Convert to trait-level TransportPacket (zero-copy: same Vec ownership)
    pub fn into_transport_packet(self) -> TransportPacket {
        TransportPacket {
            data: self.data,
            connection_id: self.connection_handle,
            timestamp_us: self.timestamp_us,
            stream_id: self.stream_id,
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

    /// Pointer to data (for FFI access)
    pub fn as_ptr(&self) -> *const u8 {
        self.data.as_ptr()
    }
}

/// Internal statistics snapshot (mapped to TransportStats)
///
/// Maintains the domain-specific representation before conversion
/// to the krepis-core transport trait layer.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct QuicServerStats {
    pub total_requests: u64,
    pub active_connections: u32,
    pub total_bytes_in: u64,
    pub total_bytes_out: u64,
    pub avg_latency_ms: f64,
    pub error_count: u64,
    pub uptime_ms: u64,
}

impl QuicServerStats {
    /// Convert to trait-level TransportStats
    pub fn into_transport_stats(self) -> TransportStats {
        TransportStats {
            total_packets_received: self.total_requests,
            active_connections: self.active_connections,
            total_bytes_in: self.total_bytes_in,
            total_bytes_out: self.total_bytes_out,
            error_count: self.error_count,
            uptime_ms: self.uptime_ms,
            avg_latency_ms: self.avg_latency_ms,
        }
    }

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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn packet_buffer_creation() {
        let data = vec![1, 2, 3, 4, 5];
        let expected_ptr = data.as_ptr();
        let expected_len = data.len();

        let packet = PacketBuffer::new(data, 42);

        assert_eq!(packet.connection_handle, 42);
        assert_eq!(packet.len(), 5);
        assert_eq!(packet.len(), expected_len);
        assert_eq!(
            packet.as_ptr(),
            expected_ptr,
            "PacketBuffer must preserve original Vec allocation (zero-copy requirement)"
        );
    }

    #[test]
    fn packet_buffer_conversion() {
        let packet = PacketBuffer::new(vec![1, 2, 3], 10);
        let transport_packet = packet.into_transport_packet();

        assert_eq!(transport_packet.connection_id, 10);
        assert_eq!(transport_packet.len(), 3);
    }

    #[test]
    fn quic_server_stats_creation() {
        let stats = QuicServerStats {
            total_requests: 100,
            active_connections: 5,
            total_bytes_in: 1000,
            total_bytes_out: 500,
            avg_latency_ms: 10.5,
            error_count: 2,
            uptime_ms: 60000,
        };

        assert_eq!(stats.total_requests, 100);
        assert_eq!(stats.active_connections, 5);
    }

    #[test]
    fn quic_server_stats_conversion() {
        let stats = QuicServerStats {
            total_requests: 50,
            active_connections: 3,
            total_bytes_in: 500,
            total_bytes_out: 250,
            avg_latency_ms: 5.0,
            error_count: 1,
            uptime_ms: 30000,
        };

        let transport_stats = stats.into_transport_stats();
        assert_eq!(transport_stats.total_packets_received, 50);
        assert_eq!(transport_stats.active_connections, 3);
    }

    #[test]
    fn quic_server_stats_serialization() {
        let stats = QuicServerStats {
            total_requests: 100,
            active_connections: 5,
            total_bytes_in: 1000,
            total_bytes_out: 500,
            avg_latency_ms: 10.5,
            error_count: 2,
            uptime_ms: 60000,
        };

        let json_bytes = stats.to_json_bytes().expect("serialization failed");
        let deserialized = QuicServerStats::from_json_bytes(&json_bytes)
            .expect("deserialization failed");

        assert_eq!(deserialized.total_requests, 100);
        assert_eq!(deserialized.active_connections, 5);
    }
}