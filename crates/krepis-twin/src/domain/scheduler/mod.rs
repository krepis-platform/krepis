//! Scheduler Module - SchedulerOracle Implementation
//!
//! # Overview
//!
//! This module implements the SchedulerOracle as specified in
//! `specs/tla/SchedulerOracle.tla`. The scheduler manages thread states and
//! determines execution order for concurrent tasks.
//!
//! # Module Structure
//!
//! ```text
//! domain/scheduler/
//! ├── types.rs              ✓ Basic types (ThreadId, ThreadState, etc.)
//! ├── backend.rs            ✓ SchedulerBackend trait
//! ├── production_backend.rs ⏳ Production implementation (DashMap)
//! ├── verification_backend.rs ⏳ Verification implementation (Fixed array)
//! ├── oracle.rs             ⏳ SchedulerOracle implementation
//! └── mod.rs                ✓ This file
//! ```
//!
//! # TLA+ Correspondence
//!
//! The scheduler implements the following TLA+ specification:
//!
//! ```tla
//! ---------------------------- MODULE SchedulerOracle ----------------------------
//! EXTENDS Integers, Sequences, FiniteSets, TLC
//!
//! CONSTANTS MaxTimeNs, MaxEvents, Threads, LamportMod, Strategy
//! VARIABLES virtualTimeNs, lamportClock, eventQueue, threadStates
//!
//! Init ==
//!     /\ virtualTimeNs = 0
//!     /\ lamportClock = 0
//!     /\ eventQueue = {}
//!     /\ threadStates = [t \in Threads |-> "RUNNABLE"]
//!
//! Next ==
//!     \/ \E t \in Threads, d \in {1, 5} : ScheduleEvent(t, d)
//!     \/ ExecuteNext_Production
//!     \/ ExecuteNext_Verification
//! ```
//!
//! # Design Philosophy
//!
//! ## Hybrid Architecture
//!
//! The scheduler uses a hybrid approach where it owns a VirtualClock for time
//! management and adds thread state management on top. This keeps the clock
//! simple (responsible only for time and events) while the scheduler handles
//! higher-level concerns (threads, blocking, dependencies).
//!
//! ## Zero-cost Abstraction
//!
//! Like other domain modules, the scheduler uses:
//! - Generic type parameters for backend selection
//! - Static dispatch via monomorphization  
//! - Inline-heavy implementations for hot paths
//! - Zero-sized types where possible
//!
//! When you write `ProductionScheduler`, the compiler generates specialized code
//! with no abstraction overhead. When you write `VerificationScheduler`, you get
//! a different specialization optimized for bounded model checking.
//!
//! ## Dual-Mode Operation
//!
//! - **PRODUCTION Mode**: Deterministic scheduling for reproducible simulations
//! - **VERIFICATION Mode**: Non-deterministic scheduling for exhaustive testing
//!
//! The mode is selected via the `SchedulingStrategy` type and compiled into the
//! binary. There is no runtime branching.
//!
//! # Usage Example (Future)
//!
//! ```rust,ignore
//! use krepis_twin::domain::scheduler::{ProductionScheduler, ThreadId};
//! use krepis_twin::domain::clock::{ProductionBackend as ClockBackend, TimeMode};
//!
//! // Create scheduler with 4 threads
//! let clock_backend = ClockBackend::new();
//! let clock = VirtualClock::new(clock_backend, TimeMode::EventDriven);
//! let mut scheduler = ProductionScheduler::new(clock, 4);
//!
//! // Schedule a task for thread 0
//! scheduler.schedule_task(ThreadId::new(0), 100, payload).unwrap();
//!
//! // Execute next runnable event
//! scheduler.execute_next().unwrap();
//! ```
//!
//! # Phase 1A Scope
//!
//! For Phase 1A, we implement:
//! - ✓ Basic types (ThreadId, ThreadState, SchedulingStrategy)
//! - ✓ Backend abstraction (SchedulerBackend trait)
//! - ⏳ Production backend (heap-allocated, concurrent)
//! - ⏳ Verification backend (stack-allocated, bounded)
//! - ⏳ SchedulerOracle core (event scheduling and execution)
//!
//! # Phase 1B Extensions
//!
//! Phase 1B will add:
//! - Resource tracking (mutexes, semaphores)
//! - Dependency management (task A depends on task B)
//! - Deadlock detection (cycle detection in dependency graph)
//! - Priority inversion detection
//! - Livelock detection

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Module Declarations
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

pub mod types;
pub mod backend;

// Future modules (to be implemented)
// pub mod production_backend;
// pub mod verification_backend;
// pub mod oracle;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Public Re-exports (Flattened API)
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// Types
pub use types::{
    SchedulerError,
    SchedulingStrategy,
    TaskId,
    ThreadId,
    ThreadState,
};

// Backend abstraction
pub use backend::{SchedulerBackend, SchedulerBackendExt};

// Backend implementations (when ready)
// pub use production_backend::ProductionBackend as ProductionSchedulerBackend;
// pub use verification_backend::VerificationBackend as VerificationSchedulerBackend;

// SchedulerOracle (when ready)
// pub use oracle::SchedulerOracle;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Type Aliases for Convenience (Future)
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// These will be uncommented when oracle.rs is implemented

// /// Production scheduler with heap allocation and concurrent access
// ///
// /// # Configuration
// /// - Backend: ProductionSchedulerBackend (DashMap for thread states)
// /// - Clock: ProductionBackend (BinaryHeap for events)
// /// - Strategy: Deterministic (PRODUCTION mode)
// ///
// /// # Characteristics
// /// - Heap-allocated: Can handle thousands of threads
// /// - Thread-safe: Safe for concurrent access
// /// - Deterministic: Same inputs → same outputs
// /// - High performance: Lock-free hot paths
// pub type ProductionScheduler = SchedulerOracle<
//     ProductionSchedulerBackend,
//     crate::domain::clock::ProductionBackend,
// >;

// /// Verification scheduler with stack allocation and bounded capacity
// ///
// /// # Configuration
// /// - Backend: VerificationSchedulerBackend (Fixed array for thread states)
// /// - Clock: VerificationBackend (Fixed array for events)
// /// - Strategy: Non-deterministic (VERIFICATION mode)
// ///
// /// # Characteristics
// /// - Stack-allocated: No heap allocation
// /// - Bounded: Fixed number of threads (typically 4)
// /// - Single-threaded: No locks needed
// /// - Kani-friendly: Suitable for formal verification
// pub type VerificationScheduler = SchedulerOracle<
//     VerificationSchedulerBackend,
//     crate::domain::clock::VerificationBackend,
// >;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Documentation Tests
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/// # Module Organization
///
/// The scheduler module is organized following Domain-Driven Design principles:
///
/// ## Core Domain Types (`types.rs`)
/// These are the fundamental building blocks that appear in the TLA+ specification:
/// - `ThreadId`: Identifies a thread
/// - `TaskId`: Identifies a unit of work  
/// - `ThreadState`: RUNNABLE | BLOCKED | COMPLETED
/// - `SchedulingStrategy`: PRODUCTION | VERIFICATION
///
/// ## Backend Abstraction (`backend.rs`)
/// The `SchedulerBackend` trait abstracts thread state storage, allowing different
/// implementations for different use cases while maintaining the same oracle logic.
///
/// ## Concrete Backends
/// - **ProductionBackend**: Uses `DashMap<ThreadId, ThreadState>` for concurrent
///   access with dynamic capacity. Optimized for real-world deployment.
///
/// - **VerificationBackend**: Uses `[ThreadState; MAX_THREADS]` for bounded
///   model checking. Optimized for formal verification with Kani.
///
/// ## SchedulerOracle (`oracle.rs`)
/// The main implementation that combines a VirtualClock with thread state management.
/// It implements the TLA+ specification's scheduling algorithm.
///
/// # Relationship to VirtualClock
///
/// The scheduler has a "has-a" relationship with VirtualClock rather than "is-a":
///
/// ```text
/// SchedulerOracle<SB, CB>
///   ├─ scheduler_backend: SB  (thread states)
///   └─ clock: VirtualClock<CB> (time and events)
/// ```
///
/// This composition allows:
/// - VirtualClock stays simple (only time/events)
/// - SchedulerOracle adds scheduling concerns (threads/blocking)
/// - Clear separation of responsibilities
/// - Easy testing of each component
///
/// # TLA+ to Rust Mapping
///
/// | TLA+ Construct | Rust Implementation |
/// |----------------|---------------------|
/// | `Threads` constant | `num_threads` parameter |
/// | `Strategy` constant | `SchedulingStrategy` enum |
/// | `threadStates` variable | `SchedulerBackend` storage |
/// | `virtualTimeNs` variable | `VirtualClock::now_ns()` |
/// | `lamportClock` variable | `VirtualClock::lamport()` |
/// | `eventQueue` variable | `VirtualClock` internal queue |
/// | `Init` action | `SchedulerOracle::new()` |
/// | `ScheduleEvent` action | `SchedulerOracle::schedule_task()` |
/// | `ExecuteNext` action | `SchedulerOracle::execute_next()` |
///
/// # Zero-cost Guarantees
///
/// When compiled, the scheduler achieves zero abstraction overhead through:
///
/// 1. **Monomorphization**: Each `SchedulerOracle<SB, CB>` instantiation gets
///    its own specialized code with no runtime polymorphism.
///
/// 2. **Inline Expansion**: Hot path methods like `is_runnable()` are inlined,
///    eliminating function call overhead.
///
/// 3. **Constant Propagation**: Strategy selection (PRODUCTION vs VERIFICATION)
///    happens at compile time, eliminating branches.
///
/// 4. **Dead Code Elimination**: Unused strategy paths are removed from the binary.
///
/// The result: Hand-written performance with abstraction benefits.
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_types_are_exported() {
        // Verify all types are accessible
        let _tid = ThreadId::new(0);
        let _task = TaskId::new(0);
        let _state = ThreadState::Runnable;
        let _strategy = SchedulingStrategy::Production;
    }

    #[test]
    fn test_thread_state_transitions() {
        // Document valid state transitions
        let initial = ThreadState::Runnable;
        assert!(initial.is_runnable());

        let blocked = ThreadState::Blocked;
        assert!(!blocked.is_runnable());

        let completed = ThreadState::Completed;
        assert!(!completed.is_runnable());
    }

    #[test]
    fn test_error_types() {
        // Verify error types are usable
        let err = SchedulerError::NoRunnableEvents;
        let msg = format!("{}", err);
        assert!(msg.contains("No runnable events"));
    }
}