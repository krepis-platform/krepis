//! # QUIC Server Configuration
//!
//! FFI-safe configuration structures for QUIC server initialization.
//! This module defines the contract for transport configuration across
//! the Rust-Deno boundary.

use super::primitives::FfiBuffer;

/// QUIC Server Configuration
///
/// Passed to QUIC server startup via FFI boundary.
/// Contains both fixed-size fields and variable-length buffers via FfiBuffer.
///
/// **Memory Layout (112 bytes, 8-byte aligned)**:
/// - Offset 0: `port` (u16, 2 bytes)
/// - Offset 2: `_padding1` (u16, 2 bytes)
/// - Offset 4: `max_streams` (u32, 4 bytes)
/// - Offset 8: `idle_timeout_ms` (u64, 8 bytes)
/// - Offset 16: `host_addr` (FfiBuffer, 32 bytes)
/// - Offset 48: `cert_path` (FfiBuffer, 32 bytes)
/// - Offset 80: `key_path` (FfiBuffer, 32 bytes)
///
/// Total: 112 bytes (8-byte aligned)
#[repr(C, align(8))]
#[derive(Debug, Clone)]
pub struct FfiQuicConfig {
    /// UDP port to listen on
    pub port: u16,

    /// Padding for alignment
    pub _padding1: u16,

    /// Maximum concurrent streams per connection
    pub max_streams: u32,

    /// Connection idle timeout in milliseconds
    pub idle_timeout_ms: u64,

    /// Host address to bind to (e.g., "127.0.0.1" or "0.0.0.0")
    /// FfiBuffer: Null-terminated string
    pub host_addr: FfiBuffer,

    /// Path to TLS certificate file (PEM format)
    /// FfiBuffer: Null-terminated path string
    pub cert_path: FfiBuffer,

    /// Path to TLS private key file (PEM format)
    /// FfiBuffer: Null-terminated path string
    pub key_path: FfiBuffer,
}

impl FfiQuicConfig {
    /// Create a new QUIC configuration with defaults
    pub fn new() -> Self {
        Self {
            port: 0,
            _padding1: 0,
            max_streams: 1000,
            idle_timeout_ms: 120000,
            host_addr: FfiBuffer::new(),
            cert_path: FfiBuffer::new(),
            key_path: FfiBuffer::new(),
        }
    }

    /// Verify configuration validity
    pub fn is_valid(&self) -> bool {
        // 기본 포트/제한 검증
        if self.port == 0 || self.max_streams == 0 || self.idle_timeout_ms == 0 {
            return false;
        }
    
        // 버퍼의 구조적 안정성 및 데이터 존재 여부 동시 검증
        let buffers_ok = self.host_addr.is_valid() && self.host_addr.len > 0
            && self.cert_path.is_valid() && self.cert_path.len > 0
            && self.key_path.is_valid() && self.key_path.len > 0;
    
        buffers_ok
    }
}

impl Default for FfiQuicConfig {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::mem;

    #[test]
    fn ffi_quic_config_size_and_align() {
        assert_eq!(
            mem::align_of::<FfiQuicConfig>(),
            8,
            "FfiQuicConfig must be 8-byte aligned"
        );
        // Size should be multiple of 8
        assert_eq!(
            mem::size_of::<FfiQuicConfig>() % 8,
            0,
            "FfiQuicConfig size must be multiple of 8"
        );
    }

    #[test]
    fn ffi_quic_config_creation() {
        let config = FfiQuicConfig::new();

        assert_eq!(config.port, 0);
        assert_eq!(config.max_streams, 1000);
        assert_eq!(config.idle_timeout_ms, 120000);
    }

    #[test]
    fn ffi_quic_config_validation_port_zero() {
        let config = FfiQuicConfig::new();
        assert!(!config.is_valid(), "Port 0 should be invalid");
    }

    #[test]
    fn ffi_quic_config_validation_zero_streams() {
        let mut config = FfiQuicConfig::new();
        config.port = 8080;
        config.max_streams = 0;
        assert!(!config.is_valid(), "Zero streams should be invalid");
    }

    #[test]
    fn ffi_quic_config_validation_zero_timeout() {
        let mut config = FfiQuicConfig::new();
        config.port = 8080;
        config.idle_timeout_ms = 0;
        assert!(!config.is_valid(), "Zero timeout should be invalid");
    }

    #[test]
    fn ffi_quic_config_validation_missing_buffers() {
        let mut config = FfiQuicConfig::new();
        config.port = 8080;
        // All buffers are empty/invalid, so config should be invalid
        assert!(!config.is_valid(), "Empty buffers should be invalid");
    }

    #[test]
    fn ffi_quic_config_valid_minimal() {
        let mut config = FfiQuicConfig::new();
        config.port = 8080;
        
        // Create valid but empty FfiBuffers by setting data to non-null
        let dummy_data = [0u8; 10];
        config.host_addr = FfiBuffer {
            data: dummy_data.as_ptr() as *mut u8,
            len: 9,
            cap: 10,
            _padding: 0,
        };
        config.cert_path = FfiBuffer {
            data: dummy_data.as_ptr() as *mut u8,
            len: 1,
            cap: 10,
            _padding: 0,
        };
        config.key_path = FfiBuffer {
            data: dummy_data.as_ptr() as *mut u8,
            len: 1,
            cap: 10,
            _padding: 0,
        };

        assert!(config.is_valid(), "Config with valid port and buffers should be valid");
    }

    #[test]
    fn ffi_quic_config_default() {
        let config = FfiQuicConfig::default();
        assert_eq!(config.port, 0);
        assert_eq!(config.max_streams, 1000);
    }
}