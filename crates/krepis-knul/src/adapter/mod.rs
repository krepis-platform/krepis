//! Adapter Layer
//!
//! Protocol-specific implementations of abstract transport and runtime interfaces.
//! Provides concrete adapters for external systems (quinn QUIC, etc.) while
//! maintaining independence from business logic.
//!
//! The adapter layer provides:
//! - **ffi**: FFI entry point handlers
//! - **quinn**: Quinn-based QUIC transport implementation
//!   - handler: Per-connection packet processing
//!   - server: Endpoint lifecycle and statistics
//!   - mod: SovereignTransport trait implementation

pub mod ffi;
pub mod quinn;