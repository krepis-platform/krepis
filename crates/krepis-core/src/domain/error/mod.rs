//! Error Module
//!
//! Defines unified error types and codes that traverse FFI boundaries between
//! Rust and Deno environments. All error codes are organized by severity and
//! domain, with FFI-safe u32 representation for Sovereign Bridge ABI v1.1.0 compatibility.

mod codes;

// Re-export error types and result alias at module level
pub use codes::KrepisError;

/// Krepis Result type for convenience
///
/// Standard Result type wrapper using KrepisError as the error variant.
/// Provides ergonomic error handling across the Krepis stack.
pub type KrepisResult<T> = Result<T, KrepisError>;