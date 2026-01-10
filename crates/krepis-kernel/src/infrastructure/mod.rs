//! Infrastructure Layer
//! 
//! This layer contains all infrastructure concerns that bridge the domain
//! layer to external systems:
//! 
//! - **serialization**: Protobuf protocol and domain-to-proto conversions (v2.0)
//! - **proto**: Legacy Protobuf module (deprecated, use serialization instead)
//! - **v8_ffi**: V8 FFI bridge and performance measurement utilities
//! 
//! # Architecture Principles
//! 
//! - Domain layer knows nothing about infrastructure
//! - Infrastructure adapts domain concepts to external protocols
//! - All external dependencies isolated here
//! 
//! # Example: Domain to Protobuf (v2.0)
//! 
//! ```ignore
//! use krepis_kernel::domain::TenantTier;
//! use krepis_kernel::infrastructure::serialization::{KrepisContext, serialize};
//! 
//! // Create context for Standard FFI execution
//! let ctx = KrepisContext::new_standard(
//!     "req-123".into(),
//!     "tenant-abc".into(),
//!     TenantTier::Standard,
//! );
//! 
//! // Serialize to bytes
//! let bytes = serialize(&ctx)?;
//! ```
//! 
//! # Example: Turbo Zero-Copy Context
//! 
//! ```ignore
//! use krepis_kernel::infrastructure::serialization::KrepisContext;
//! use krepis_kernel::domain::TenantTier;
//! 
//! // Create context for Turbo execution with slot allocation
//! let ctx = KrepisContext::new_turbo(
//!     "req-456".into(),
//!     "tenant-xyz".into(),
//!     TenantTier::Turbo,
//!     42, // slot_index
//! );
//! 
//! assert!(ctx.uses_turbo());
//! assert_eq!(ctx.get_turbo_slot(), Some(42));
//! ```
//! 
//! # Example: Performance Measurement
//! 
//! ```ignore
//! use krepis_kernel::infrastructure::v8_ffi::PerfTimer;
//! 
//! let timer = PerfTimer::start();
//! // ... execute code ...
//! let elapsed_ns = timer.elapsed_ns();
//! println!("Execution took: {}ns", elapsed_ns);
//! ```

pub mod serialization;  // v2.0 - Primary serialization module
//pub mod v8_ffi;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Primary API (v2.0)
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

pub use serialization::{
    KrepisContext,
    KrepisError,
    FfiResponse,
    FfiEnvelope,
    MessageType,
    ErrorCode,
    ErrorCategory,
    PROTOCOL_VERSION,
    TURBO_SLOT_NONE,
    serialize,
    deserialize,
    create_envelope,
    extract_payload,
};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Performance Utilities
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

pub use v8_ffi::{PerfTimer, ScopedTimer, PerfSnapshot};