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

// Re-export primary types
pub use domain::{
    EventId,
    EventPayload,
    LamportClock,
    ScheduledEvent,
    TimeMode,
    VirtualClock,
    VirtualTimeNs,
};
pub use domain::{
    Address,
    Value,
    CoreId,
    StoreEntry,
    MemoryOp,
    ConsistencyModel,
    MemoryConfig,
    SimulatedMemory,
};
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
}