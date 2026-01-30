//! # Sovereign Bridge ABI v1.1.0
//!
//! Low-level FFI memory layout definitions for Rust-Deno zero-copy bridge.
//! All structures use `#[repr(C)]` with explicit alignment for ABI stability.
//!
//! ## Design Principles
//!
//! The Sovereign Bridge ABI establishes a stable contract between the Krepis
//! kernel (Rust) and the TypeScript SDK (Deno) running in separate processes.
//! This ABI defines:
//!
//! - Explicit memory layouts with compile-time verification
//! - Pointer safety guarantees across process boundaries
//! - Thread-safe data transfer mechanisms
//! - Version compatibility checking
//!
//! ## Module Organization
//!
//! - `primitives`: Basic FFI types (FfiBuffer, FfiResponse, FfiLockState)
//! - `config`: QUIC server configuration structures
//! - `shared`: Shared memory coordination metadata

pub mod config;
pub mod primitives;
pub mod shared;

// Re-export all ABI types at module level
pub use config::FfiQuicConfig;
pub use primitives::{FfiBuffer, FfiLockState, FfiResponse};
pub use shared::SharedMemoryMetadata;