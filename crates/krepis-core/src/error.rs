//! # Unified Error Types & Codes
//!
//! Sovereign Bridge ABI v1.1.0 - Error Propagation
//! All error codes are FFI-compatible (u32) and cross the Rust-Deno boundary.

use std::fmt;

/// Krepis error codes for FFI boundary
///
/// `#[repr(u32)]` ensures compatibility with C FFI and shared memory protocols.
/// Error codes are organized by severity and domain.
#[repr(u32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KrepisError {
    /// Successful operation (0x0000)
    Success = 0,

    // === Internal Errors (0x1000-0x1FFF) ===
    /// Generic internal error (e.g., panic, unrecoverable state)
    Internal = 1000,
    /// Context is missing or invalid
    InvalidContext = 1001,
    /// ABI version mismatch detected
    AbiMismatch = 1002,
    /// Memory layout violation or alignment error
    MemoryAlignment = 1003,
    /// Pointer validation failed (null, out of bounds, etc.)
    InvalidPointer = 1004,

    // === Timeout Errors (0x2000-0x2FFF) ===
    /// Operation exceeded deadline (Watchdog triggered)
    Timeout = 2000,
    /// Kernel operation timeout
    KernelTimeout = 2001,
    /// SDK operation timeout
    SdkTimeout = 2002,
    /// Lock acquisition timeout
    LockTimeout = 2003,

    // === Resource Errors (0x3000-0x3FFF) ===
    /// Resource quota exceeded (Resource Guard violation)
    QuotaExceeded = 3000,
    /// Memory allocation failed
    OutOfMemory = 3001,
    /// CPU credit exhausted
    CpuQuotaExceeded = 3002,
    /// Concurrent request limit reached
    ConcurrencyLimitExceeded = 3003,
    /// Connection pool exhausted
    PoolExhausted = 3004,

    // === Validation Errors (0x4000-0x4FFF) ===
    /// Handshake failed (ABI capability mismatch)
    HandshakeFailed = 4000,
    /// Invalid request format or schema
    InvalidRequest = 4001,
    /// Unsupported operation version
    VersionMismatch = 4002,
    /// Tenant not found or inactive
    TenantNotFound = 4003,
    /// Authorization check failed
    Unauthorized = 4004,

    // === Network Errors (0x5000-0x5FFF) ===
    /// Network communication failure
    NetworkError = 5000,
    /// Connection refused or reset
    ConnectionFailed = 5001,
    /// Serialization/deserialization failed
    SerializationError = 5002,

    // === Domain-Specific Errors (0x6000-0x6FFF) ===
    /// Twin/formal verification error
    VerificationError = 6000,
    /// Kernel isolate pool error
    IsolatePoolError = 6001,
    /// Scheduler error (DPOR, Ki-DPOR, etc.)
    SchedulerError = 6002,
}

impl KrepisError {
    /// Convert error code back to enum variant (lossy for unknown codes)
    pub fn from_code(code: u32) -> Self {
        match code {
            0 => KrepisError::Success,
            1000 => KrepisError::Internal,
            1001 => KrepisError::InvalidContext,
            1002 => KrepisError::AbiMismatch,
            1003 => KrepisError::MemoryAlignment,
            1004 => KrepisError::InvalidPointer,
            2000 => KrepisError::Timeout,
            2001 => KrepisError::KernelTimeout,
            2002 => KrepisError::SdkTimeout,
            2003 => KrepisError::LockTimeout,
            3000 => KrepisError::QuotaExceeded,
            3001 => KrepisError::OutOfMemory,
            3002 => KrepisError::CpuQuotaExceeded,
            3003 => KrepisError::ConcurrencyLimitExceeded,
            3004 => KrepisError::PoolExhausted,
            4000 => KrepisError::HandshakeFailed,
            4001 => KrepisError::InvalidRequest,
            4002 => KrepisError::VersionMismatch,
            4003 => KrepisError::TenantNotFound,
            4004 => KrepisError::Unauthorized,
            5000 => KrepisError::NetworkError,
            5001 => KrepisError::ConnectionFailed,
            5002 => KrepisError::SerializationError,
            6000 => KrepisError::VerificationError,
            6001 => KrepisError::IsolatePoolError,
            6002 => KrepisError::SchedulerError,
            _ => KrepisError::Internal, // Unknown codes map to Internal
        }
    }

    /// Get human-readable error message
    pub fn message(&self) -> &'static str {
        match self {
            KrepisError::Success => "Success",
            KrepisError::Internal => "Internal error",
            KrepisError::InvalidContext => "Invalid context",
            KrepisError::AbiMismatch => "ABI version mismatch",
            KrepisError::MemoryAlignment => "Memory alignment violation",
            KrepisError::InvalidPointer => "Invalid pointer",
            KrepisError::Timeout => "Operation timeout",
            KrepisError::KernelTimeout => "Kernel operation timeout",
            KrepisError::SdkTimeout => "SDK operation timeout",
            KrepisError::LockTimeout => "Lock acquisition timeout",
            KrepisError::QuotaExceeded => "Resource quota exceeded",
            KrepisError::OutOfMemory => "Out of memory",
            KrepisError::CpuQuotaExceeded => "CPU quota exceeded",
            KrepisError::ConcurrencyLimitExceeded => "Concurrency limit exceeded",
            KrepisError::PoolExhausted => "Connection pool exhausted",
            KrepisError::HandshakeFailed => "Handshake failed",
            KrepisError::InvalidRequest => "Invalid request",
            KrepisError::VersionMismatch => "Version mismatch",
            KrepisError::TenantNotFound => "Tenant not found",
            KrepisError::Unauthorized => "Unauthorized",
            KrepisError::NetworkError => "Network error",
            KrepisError::ConnectionFailed => "Connection failed",
            KrepisError::SerializationError => "Serialization error",
            KrepisError::VerificationError => "Verification error",
            KrepisError::IsolatePoolError => "Isolate pool error",
            KrepisError::SchedulerError => "Scheduler error",
        }
    }

    /// Check if error is retryable
    pub fn is_retryable(&self) -> bool {
        matches!(
            self,
            KrepisError::Timeout
                | KrepisError::KernelTimeout
                | KrepisError::SdkTimeout
                | KrepisError::LockTimeout
                | KrepisError::NetworkError
                | KrepisError::ConnectionFailed
                | KrepisError::PoolExhausted
        )
    }

    /// Check if error is a resource exhaustion issue
    pub fn is_resource_error(&self) -> bool {
        matches!(
            self,
            KrepisError::QuotaExceeded
                | KrepisError::OutOfMemory
                | KrepisError::CpuQuotaExceeded
                | KrepisError::ConcurrencyLimitExceeded
                | KrepisError::PoolExhausted
        )
    }
}

impl fmt::Display for KrepisError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "KrepisError::{:?} (0x{:04x}): {}",
            self,
            *self as u32,
            self.message()
        )
    }
}

impl std::error::Error for KrepisError {}

/// Krepis Result type for convenience
pub type KrepisResult<T> = Result<T, KrepisError>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn error_code_round_trip() {
        let err = KrepisError::AbiMismatch;
        let code = err as u32;
        let recovered = KrepisError::from_code(code);
        assert_eq!(err, recovered);
    }

    #[test]
    fn error_messages_non_empty() {
        for code in [
            KrepisError::Success,
            KrepisError::Timeout,
            KrepisError::QuotaExceeded,
        ] {
            assert!(!code.message().is_empty());
        }
    }

    #[test]
    fn retryable_errors() {
        assert!(KrepisError::Timeout.is_retryable());
        assert!(KrepisError::NetworkError.is_retryable());
        assert!(!KrepisError::Unauthorized.is_retryable());
    }

    #[test]
    fn resource_errors() {
        assert!(KrepisError::QuotaExceeded.is_resource_error());
        assert!(KrepisError::OutOfMemory.is_resource_error());
        assert!(!KrepisError::Timeout.is_resource_error());
    }
}