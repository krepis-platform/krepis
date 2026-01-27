//! # Krepis Core
//!
//! Shared abstraction layer between Kernel and KNUL.
//! Defines FFI boundaries, context propagation contracts, and error codes.
//!
//! ## Module Organization
//!
//! - `abi`: FFI-safe memory layouts (Sovereign Bridge ABI v1.1.0)
//! - `context`: Context propagation structures
//! - `error`: Unified error types and codes
//! - `traits`: Kernel and runtime behavior contracts

pub mod abi;
pub mod context;
pub mod error;
pub mod traits;

// Re-export commonly used types
pub use abi::{FfiBuffer, FfiResponse, FfiLockState};
pub use context::SovereignContext;
pub use error::KrepisError;
pub use traits::{SovereignRuntime, ResourceGuard};

/// Library version
pub const KREPIS_CORE_VERSION: &str = "0.1.0";

/// ABI version for compatibility checking
pub const FFI_ABI_VERSION: u32 = 1u32 << 16 | 1u32; // 1.1.0