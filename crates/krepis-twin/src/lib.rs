//! Krepis Digital Twin Simulator
//! 
//! # Overview
//! 
//! `krepis-twin` is a deterministic digital twin simulator that models
//! the Krepis runtime environment with microsecond precision and formal
//! verification guarantees.
//!
//! # Quick Start
//! 
//! ```rust
//! use krepis_twin::ProductionSimulatorBuilder;
//! 
//! // Use the builder to configure and create the simulator
//! let mut sim = ProductionSimulatorBuilder::new()
//!     .num_cores(4)
//!     .buffer_size(2)
//!     .build();
//! 
//! // Write to memory (buffered)
//! sim.memory_mut().write(0, 0x1000, 42).unwrap();
//! 
//! // Run simulation until all events are processed
//! sim.run_until_idle();
//! 
//! // Verify the write was flushed to main memory
//! assert_eq!(sim.memory().read_main_memory(0x1000), 42);
//! ```
//!
//! # Phase 2 Integration (KNUL FFI)
//!
//! For KNUL integration, use the ergonomic top-level exports:
//!
//! ```rust
//! use krepis_twin::{Simulator, ThreadId, ResourceId};
//! 
//! #[cfg(feature = "twin")]
//! use krepis_twin::{KiDporScheduler, LivenessViolation, Operation};
//! ```
//!
//! # Builder Pattern
//!
//! The simulator uses a builder pattern for flexible configuration:
//!
//! ```rust
//! use krepis_twin::ProductionSimulatorBuilder;
//! 
//! let mut sim = ProductionSimulatorBuilder::new()
//!     .num_cores(8)              // Set number of cores
//!     .buffer_size(4)            // Set buffer size per core
//!     .enable_tracing(true)      // Enable event tracing
//!     .max_traced_events(100_000) // Limit traced events
//!     .build();
//! ```
//!
//! # With Tracing Support
//!
//! To enable observability and formal verification:
//!
//! ```rust
//! use krepis_twin::ProductionSimulatorBuilder;
//! 
//! let (mut sim, tracer) = ProductionSimulatorBuilder::new()
//!     .num_cores(4)
//!     .buffer_size(2)
//!     .enable_tracing(true)
//!     .build_with_tracer();
//! 
//! // Simulator and tracer are now ready for integrated use
//! // Tracer can record events for later analysis
//! ```
//!
//! # Architecture
//! 
//! The crate is organized into layers:
//! - **domain**: Core simulation logic (clock, memory, scheduler, resources)
//! - **Verification**: DPOR schedulers for bug hunting (feature-gated)
//!
//! # Feature Flags
//! 
//! - `twin`: Enable DPOR schedulers for formal verification (adds ~200KB to binary)
//! - `verification`: Enable Kani formal verification proofs (dev-only)

#![warn(missing_docs)]
#![warn(clippy::all)]
#![warn(clippy::pedantic)]
#![allow(clippy::module_name_repetitions)]
#![allow(clippy::must_use_candidate)]

// ============================================================================
// Domain Layer - Always Available
// ============================================================================

pub mod domain;

// ============================================================================
// Top-Level Ergonomic Re-exports
// ============================================================================

// Simulation Entry Points
pub use domain::simulation::{
    EventDispatcher,
    Simulator,
};

// Builder Pattern (CRITICAL: Export the builders, not builder methods)
pub use domain::{
    ProductionSimulator, 
    VerificationSimulator, 
    ProductionSimulatorBuilder, 
    VerificationSimulatorBuilder
};

// Resource Identifiers (Critical for KNUL mapping)
pub use domain::resources::{
    ThreadId,
    ResourceId,
    ResourceError,
    RequestResult,
};

// Memory System
pub use domain::memory::{
    MemoryConfig,
    ConsistencyModel,
};

// Clock System
pub use domain::clock::{
    TimeMode,
    VirtualTimeNs,
    EventPayload,
};

// ============================================================================
// DPOR Verification - Feature-Gated
// ============================================================================

/// DPOR types for formal verification (only with `--features twin`)
///
/// These types enable bug hunting and state space exploration during
/// development and CI. Production builds exclude this module entirely.
///
/// # Usage
///
/// ```rust
/// #[cfg(feature = "twin")]
/// use krepis_twin::{DporScheduler, KiDporScheduler, Operation, LivenessViolation};
/// 
/// #[cfg(feature = "twin")]
/// {
///     // Use Ki-DPOR for fast bug hunting
///     let scheduler = KiDporScheduler::new(4, 2);
///     
///     // Or Classic DPOR for exhaustive verification
///     let classic = DporScheduler::new(4);
/// }
/// ```
#[cfg(feature = "twin")]
pub use domain::dpor::{
    // Schedulers
    DporScheduler,
    KiDporScheduler,
    
    // Core Types
    Operation,
    StepRecord,
    VectorClock,
    
    // Liveness (Phase 1D)
    LivenessViolation,
    ThreadStatus,
    
    // State Representation
    KiState,
    
    // Statistics & Metrics
    DporStats,
    
    // Constants
    MAX_THREADS,
    MAX_DEPTH,
    MAX_STARVATION_LIMIT,
};

// ============================================================================
// Version Information
// ============================================================================

/// Crate version string
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// Phase 1 completion status
pub const PHASE_1_COMPLETE: bool = true;

/// Supported verification levels
pub const VERIFICATION_LEVELS: &[&str] = &[
    "V-1: Build Pass",
    "V-2: Unit Tests",
    "V-3: TLA+ + Kani (Critical Paths)",
    "V-4: Exhaustive Verification",
    "V-5: External Audit",
];

// ============================================================================
// Feature Flags Documentation
// ============================================================================

// Note: We intentionally allow `twin` feature in release builds.
// High-performance verification (Ki-DPOR) requires compiler optimizations
// to explore vast state spaces efficiently.
//
// Production builds should strictly use:
// `cargo build --release --no-default-features`

// #[cfg(all(feature = "twin", not(debug_assertions)))]
// compile_error!(
//     "The `twin` feature should not be enabled in release builds. \
//      Use `cargo build --release --no-default-features` for production."
// );