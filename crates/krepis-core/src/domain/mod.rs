//! Domain Layer
//!
//! Encapsulates all domain-specific logic and types that form the core
//! business abstractions of the Krepis platform. The domain layer is
//! independent of infrastructure concerns and remains the authoritative
//! source for entity definitions and behavior.
//!
//! Organized into multiple behavioral domains:
//! - **context**: Execution context propagation (Deterministic Context principle)
//! - **error**: Unified error types and codes (FFI-safe error handling)
//! - **runtime**: Runtime lifecycle and execution contracts
//! - **resource**: Resource quota enforcement and usage tracking
//! - **kernel**: Kernel capabilities and reverse-call interfaces
//! - **transport**: Network transport abstraction (Abstraction Barrier principle)

pub mod context;
pub mod error;
pub mod kernel;
pub mod resource;
pub mod runtime;
pub mod transport;

// Re-export commonly used domain types at the domain layer level
pub use context::{ContextBuilder, SovereignContext};
pub use error::{KrepisError, KrepisResult};
pub use kernel::KernelCapabilities;
pub use resource::{ResourceGuard, ResourceType, ResourceUsage};
pub use runtime::{RuntimeStats, SovereignRuntime};
pub use transport::{SovereignTransport, TransportFactory, TransportPacket, TransportStats};