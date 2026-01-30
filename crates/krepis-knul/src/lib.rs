//! # Krepis KNUL - Network Adapter Layer
//!
//! FFI bridge between Deno TypeScript SDK and Krepis Kernel.
//! Manages QUIC server lifecycle and handles network communication.
//!
//! ## Architecture
//!
//! ```text
//! ┌──────────────────────────┐
//! │   Deno TypeScript        │
//! │   (KNUL Adapter)         │
//! └────────────┬─────────────┘
//!              │ FFI Boundary
//!              ▼
//! ┌──────────────────────────┐
//! │   Krepis KNUL (Rust)     │
//! │   - FFI Entry Points     │
//! │   - Server Registry      │
//! │   - QUIC Server Mgmt     │
//! └──────────────────────────┘
//! ```
//!
//! ## Module Organization
//!
//! - `domain`: Domain types for packet handling and statistics
//! - `infrastructure`: Low-level system abstractions
//!   - `registry`: Thread-safe server instance management
//!   - `queue`: Packet queue for zero-copy handoff
//!   - `runtime`: Global runtime and state management
//!   - `ffi`: FFI utility functions for type conversion
//! - `adapter`: Protocol-specific implementations
//!   - `ffi`: FFI entry point handlers
//!   - `quinn`: Quinn-based QUIC transport
//!
//! ## Features
//!
//! - **FFI-First Design**: All public functions use `extern "C"` calling convention
//! - **Handle-Based Management**: Server instances identified by u64 handles
//! - **Thread-Safe Registry**: Concurrent server instance management
//! - **Zero-Copy Buffers**: Uses `krepis-core` ABI structures
//! - **No Business Logic**: Pure communication layer (Sovereign Link principle)

pub mod adapter;
pub mod domain;
pub mod infrastructure;

// Re-export core types for convenience
pub use krepis_core::{FfiBuffer, FfiResponse, FfiQuicConfig, KrepisError};

/// Library version
pub const KREPIS_KNUL_VERSION: &str = "0.1.0";

/// FFI ABI version (must match krepis-core)
pub const FFI_ABI_VERSION: u32 = 1u32 << 16 | 1u32; // 1.1.0

#[cfg(test)]
mod lib_tests {
    use super::*;

    #[test]
    fn test_version() {
        assert_eq!(KREPIS_KNUL_VERSION, "0.1.0");
        assert_eq!(FFI_ABI_VERSION, 0x00010001);
    }
}