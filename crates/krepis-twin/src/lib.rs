//! Krepis Digital Twin Simulator
//! 
//! # Overview
//! 
//! `krepis-twin` is a deterministic digital twin simulator that models
//! the Krepis runtime environment with microsecond precision and formal
//! verification guarantees.
//!
//! # Trinity Architecture
//! 
//! This crate follows the Trinity Architecture pattern:
//! 
//! - **Domain**: Pure business logic and domain models
//! - **Infrastructure**: External technology integrations
//! - **Adapters**: Ports & Adapters connecting domain to infrastructure
//!
//! # TLA+ Verification
//! 
//! All core components are verified against TLA+ specifications:
//! 
//! - `VirtualClock`: Corresponds to `specs/tla/VirtualClock.tla`
//! - `SimulatedMemory`: Corresponds to `specs/tla/SimulatedMemory.tla`
//! - `SchedulerOracle`: Corresponds to `specs/tla/SchedulerOracle.tla`
//! - `SovereignKernel`: Corresponds to `specs/tla/SovereignKernel.tla`
//!
//! # Physical Laws (Invariants)
//! 
//! The simulator enforces these fundamental invariants:
//! 
//! ## Temporal Laws
//! - **T-001**: Time Monotonicity - Time never decreases
//! - **T-002**: Event Causality - Lamport ordering preserved
//! - **T-003**: Event Ordering - Events fire in scheduled order
//!
//! ## Memory Laws
//! - **M-001**: Sequential Consistency - SeqCst operations totally ordered
//! - **M-002**: Atomic Integrity - No torn reads/writes
//! - **M-003**: Store Buffer Semantics - Relaxed memory model
//!
//! ## Scheduler Laws
//! - **S-001**: Progress - Runnable tasks eventually run
//! - **S-002**: Deadlock Detection - Cycles detected and reported
//! - **S-003**: Fairness - No task starvation
//!
//! ## Kernel Laws
//! - **K-001**: Heap Isolation - Tenant heap limits enforced
//! - **K-002**: Watchdog Guarantee - Runaway code terminated
//! - **K-003**: Tenant Isolation - No cross-tenant access
//!
//! # Usage
//! 
//! ```rust
//! // 필요한 타입들을 명시적으로 가져옵니다.
//! use krepis_twin::domain::{ProductionSimulatorBuilder, TimeMode, MemoryConfig};
//! 
//! // 1. 빌더를 사용하여 시뮬레이터 생성
//! // ProductionSimulatorBuilder는 내부적으로 필요한 메모리와 클록 백엔드를 조립합니다.
//! let mut sim = ProductionSimulatorBuilder::new()
//!     .num_cores(4)
//!     .buffer_size(2)
//!     .build();
//! 
//! // 2. 메모리 작업 실행 (Buffered Write)
//! sim.memory_mut().write(0, 0x1000, 42).unwrap();
//! 
//! // 3. 시뮬레이션 엔진 가동 (이벤트 처리 및 메모리 플러시)
//! sim.run_until_idle();
//! 
//! // 4. 결과 확인
//! assert_eq!(sim.memory().read_main_memory(0x1000), 42);
//! ```
//! # Feature Flags
//! 
//! - `verification`: Enable Kani formal verification proofs

#![warn(missing_docs)]
#![warn(clippy::all)]
#![warn(clippy::pedantic)]
#![warn(clippy::nursery)]

// Trinity Architecture Layers
pub mod domain;
pub mod infrastructure;
pub mod adapters;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Re-export Primary Types
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// Clock types
pub use domain::{
    EventId,
    EventPayload,
    LamportClock,
    ScheduledEvent,
    TimeMode,
    VirtualClock,
    VirtualTimeNs,
};

// Memory types
pub use domain::{
    Address,
    CoreId,
    ConsistencyModel,
    MemoryConfig,
    MemoryOp,
    SimulatedMemory,
    StoreEntry,
    Value,
};

// Scheduler types (always available for both production and verification)
pub use domain::{
    SchedulerBackend,
    SchedulerError,
    SchedulerOracle,
    SchedulingStrategy,
    TaskId,
    ThreadId,
    ThreadState,
    VerificationScheduler,
    VerificationSchedulerBackend,
};

// Scheduler types (production only - excluded from Kani builds)
#[cfg(not(kani))]
pub use domain::{ProductionScheduler, ProductionSchedulerBackend};

// Simulation types
pub use domain::EventDispatcher;
// pub use adapters::Simulator;  // TODO: Step 6

/// Library version
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// TLA+ specification version this implementation corresponds to
pub const TLA_SPEC_VERSION: &str = "1.0.0";

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_version_defined() {
        assert!(!VERSION.is_empty());
    }

    #[test]
    fn test_tla_spec_version_defined() {
        assert_eq!(TLA_SPEC_VERSION, "1.0.0");
    }

    #[test]
    fn test_scheduler_types_exported() {
        // Verify core scheduler types are always available
        let _tid = ThreadId::new(0);
        let _task = TaskId::new(0);
        let _state = ThreadState::Runnable;
        let _strategy = SchedulingStrategy::Production;
    }

    #[test]
    #[cfg(not(kani))]
    fn test_production_scheduler_exported() {
        // This test only compiles in non-Kani builds
        // Verifies that ProductionScheduler is available in production
        use domain::clock::{ProductionBackend as ProdClockBackend, TimeMode, VirtualClock};
        
        let clock_backend = ProdClockBackend::new();
        let clock = VirtualClock::new(clock_backend, TimeMode::EventDriven);
        
        let _scheduler: ProductionScheduler = SchedulerOracle::new(
            clock,
            4,
            SchedulingStrategy::Production,
        );
    }

    #[test]
    fn test_verification_scheduler_always_available() {
        // This test compiles in both Kani and non-Kani builds
        use domain::clock::{VerificationBackend as VerifClockBackend, TimeMode, VirtualClock};
        
        let clock_backend = VerifClockBackend::new();
        let clock = VirtualClock::new(clock_backend, TimeMode::EventDriven);
        
        let _scheduler: VerificationScheduler = SchedulerOracle::new(
            clock,
            4,
            SchedulingStrategy::Verification,
        );
    }
}