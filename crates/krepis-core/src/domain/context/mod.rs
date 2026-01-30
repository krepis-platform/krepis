//! Context Module
//!
//! Defines context propagation structures that embody the Deterministic Context
//! principle: all async operations and domain logic explicitly receive context
//! as a parameter, eliminating implicit state propagation and ensuring complete
//! traceability and reproducibility.

mod types;

// Re-export all context types at module level for convenient access
pub use types::{ContextBuilder, SovereignContext};