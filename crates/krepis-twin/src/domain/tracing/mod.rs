//! # Tracing Domain Module
//!
//! This module provides **zero-cost observability** for the Krepis-Twin simulation engine.
//! It records simulation events with Lamport timestamps to enable:
//! - Causality analysis (happens-before relationships)
//! - Deterministic replay
//! - Formal verification of temporal invariants
//! - Marketplace-grade simulation reports
//!
//! ## Architecture Compliance
//! - **Domain Layer**: Pure business logic, no I/O dependencies
//! - **Verification-First**: All causality invariants are Kani-provable
//! - **Fractal Integrity**: Each component is a testable Super Micro Task
//! - **Zero-cost Razor**: No heap allocation in hot paths, array-based storage

pub mod event;
pub mod tracer;
pub mod causality;

#[cfg(kani)]
pub mod proofs;

// Re-exports for ergonomic usage
pub use event::{
    SimulationEvent, EventMetadata, MemoryOperation, ClockEvent, FenceType, SyncType,
    LamportTimestamp, ThreadId, MemAddr, MAX_THREADS,
};
pub use tracer::{
    EventTracer, TracerConfig, TracingError,
    ProductionBackend, VerificationBackend,
    ProductionTracer, VerificationTracer,
    TracerBackend,
};
pub use causality::{CausalityGraph, HappensBeforeRelation};

/// Version of the tracing format for backward compatibility
pub const TRACING_FORMAT_VERSION: u32 = 1;

/// Maximum events per trace (production default)
pub const DEFAULT_MAX_EVENTS: usize = 100_000;