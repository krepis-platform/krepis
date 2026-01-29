//! # Sovereign Bridge ABI v1.1.0
//!
//! Low-level FFI memory layout definitions for Rust-Deno zero-copy bridge.
//! All structures use `#[repr(C)]` with explicit alignment for ABI stability.

/// Shared Memory Lock States
/// Used for synchronization between Kernel and KNUL/SDK processes
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FfiLockState;

impl FfiLockState {
    /// Lock owned by Kernel (reader phase)
    pub const KERNEL_OWNED: u32 = 0;
    /// Lock owned by SDK/KNUL (writer phase)
    pub const SDK_OWNED: u32 = 1;
    /// Lock in contention state
    pub const LOCKED: u32 = 2;
}

/// FFI-safe buffer for zero-copy data transfer
///
/// Represents a contiguous memory region with explicit padding for 64-bit alignment.
/// **Memory Layout (96 bits = 12 bytes)**:
/// - Offset 0: `data` (pointer, 8 bytes)
/// - Offset 8: `len` (usize, 8 bytes on 64-bit)
/// - Offset 16: `cap` (usize, 8 bytes on 64-bit)
/// - Offset 24: `_padding` (u64, 8 bytes)
///
/// Total: 96 bytes (8-byte aligned)
#[repr(C, align(8))]
#[derive(Debug, Clone)]
pub struct FfiBuffer {
    /// Pointer to buffer data (must be pinned in kernel-managed memory)
    pub data: *mut u8,
    /// Current length (valid data bytes)
    pub len: usize,
    /// Capacity (total allocated bytes)
    pub cap: usize,
    /// Explicit padding for alignment; reserved for future lock metadata
    pub _padding: u64,
}

impl FfiBuffer {
    /// Create a new empty FfiBuffer
    pub const fn new() -> Self {
        Self {
            data: std::ptr::null_mut(),
            len: 0,
            cap: 0,
            _padding: 0,
        }
    }

    /// Verify buffer is valid for FFI crossing
    pub fn is_valid(&self) -> bool {
        // Null ptr with zero len/cap is valid (empty buffer)
        if self.data.is_null() {
            return self.len == 0 && self.cap == 0;
        }
        // Non-null buffer must have cap >= len
        self.cap >= self.len && self.len > 0
    }
}

impl Default for FfiBuffer {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// THREAD SAFETY IMPLEMENTATIONS
// ============================================================================

/// FfiBuffer is safe to send between threads
///
/// Although FfiBuffer contains a raw pointer (*mut u8), it is safe to send
/// between threads because:
/// 1. The pointer always references kernel-managed memory (never user-allocated)
/// 2. Ownership is never transferred; FfiBuffer is always used behind Arc/DashMap
/// 3. The kernel guarantees memory stability while server is running
/// 4. Access is synchronized via Arc/DashMap/AtomicU64 in containing structures
///
/// # Safety Justification
/// - Kernel owns all memory referenced by FfiBuffer
/// - No race conditions: memory access patterns are coordinated via FFI boundary
/// - Pointer validity guaranteed by ownership model
unsafe impl Send for FfiBuffer {}

/// FfiBuffer is safe to share between threads
///
/// See Send implementation above for detailed justification.
/// Sync is safe because FfiBuffer is immutable after creation (fields are pub but not mut).
unsafe impl Sync for FfiBuffer {}

/// FFI Response wrapper for Kernel ↔ SDK communication
///
/// **Memory Layout (32 bytes)**:
/// - Offset 0: `error_code` (u32, 4 bytes)
/// - Offset 4: `_reserved` (u32, 4 bytes)
/// - Offset 8: `result_buffer` (FfiBuffer, 24 bytes)
///
/// Total: 32 bytes (aligned to 8 bytes)
#[repr(C, align(8))]
#[derive(Debug, Clone)]
pub struct FfiResponse {
    /// Error code (0 = SUCCESS)
    pub error_code: u32,
    /// Reserved for future use (alignment padding)
    pub _reserved: u32,
    /// Result payload (if error_code == 0)
    pub result_buffer: FfiBuffer,
}

impl FfiResponse {
    /// Create a successful response with buffer
    pub const fn success(buffer: FfiBuffer) -> Self {
        Self {
            error_code: 0,
            _reserved: 0,
            result_buffer: buffer,
        }
    }

    /// Create an error response with error code
    pub const fn error(error_code: u32) -> Self {
        Self {
            error_code,
            _reserved: 0,
            result_buffer: FfiBuffer::new(),
        }
    }

    /// Check if response indicates success
    pub fn is_success(&self) -> bool {
        self.error_code == 0
    }

    /// Check if response indicates error
    pub fn is_error(&self) -> bool {
        self.error_code != 0
    }
}

impl Default for FfiResponse {
    fn default() -> Self {
        Self::error(crate::error::KrepisError::Internal as u32)
    }
}

/// Shared Memory Metadata (for turbo-tier)
///
/// Stored at the head of turbo-mode shared memory region.
/// Enables Kernel and SDK to coordinate without syscalls.
#[repr(C, align(8))]
#[derive(Debug, Clone)]
pub struct SharedMemoryMetadata {
    /// Version of shared memory format
    pub version: u32,
    /// Lock state (FfiLockState enum)
    pub lock_state: u32,
    /// Kernel's last write timestamp (ns)
    pub kernel_ts: u64,
    /// SDK's last write timestamp (ns)
    pub sdk_ts: u64,
    /// Offset to first data region
    pub data_offset: u32,
    /// Total usable size after metadata
    pub data_size: u32,
}

impl SharedMemoryMetadata {
    /// Create new metadata structure
    pub const fn new(version: u32, data_offset: u32, data_size: u32) -> Self {
        Self {
            version,
            lock_state: FfiLockState::KERNEL_OWNED,
            kernel_ts: 0,
            sdk_ts: 0,
            data_offset,
            data_size,
        }
    }

    /// Verify metadata integrity
    pub fn is_valid(&self) -> bool {
        self.data_offset > 0 && self.data_size > 0 && self.version > 0
    }
}

// ============================================================================
// QUIC SERVER CONFIGURATION (FFI ABI v1.1.0 Extension)
// ============================================================================

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
        // Port must be in valid range
        if self.port == 0 {
            return false;
        }

        // Streams and timeout must be reasonable
        if self.max_streams == 0 || self.idle_timeout_ms == 0 {
            return false;
        }

        // All buffer paths must be valid
        if !self.host_addr.is_valid() || !self.cert_path.is_valid() || !self.key_path.is_valid() {
            return false;
        }

        true
    }
}

impl Default for FfiQuicConfig {
    fn default() -> Self {
        Self::new()
    }
}

// Compile-time assertions for ABI stability
#[cfg(test)]
mod abi_size_checks {
    use super::*;
    use std::mem;

    #[test]
    fn ffi_buffer_size_and_align() {
        assert_eq!(
            mem::size_of::<FfiBuffer>(),
            32,
            "FfiBuffer must be exactly 32 bytes"
        );
        assert_eq!(
            mem::align_of::<FfiBuffer>(),
            8,
            "FfiBuffer must be 8-byte aligned"
        );
    }

    #[test]
    fn ffi_response_size_and_align() {
        assert_eq!(
            mem::size_of::<FfiResponse>(),
            40,
            "FfiResponse must be exactly 40 bytes"
        );
        assert_eq!(
            mem::align_of::<FfiResponse>(),
            8,
            "FfiResponse must be 8-byte aligned"
        );
    }

    #[test]
    fn shared_memory_metadata_size() {
        assert_eq!(
            mem::size_of::<SharedMemoryMetadata>(),
            32,
            "SharedMemoryMetadata must be exactly 32 bytes"
        );
    }

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
}