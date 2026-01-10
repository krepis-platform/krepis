//! Virtual Clock Module - The Zero-cost Razor Architecture
//!
//! # Design Philosophy
//!
//! This module implements a **trait-based backend system** that eliminates
//! all runtime overhead while supporting both production and verification modes:
//!
//! ```text
//! ┌────────────────────────────────────────────────────────┐
//! │  Application Code                                      │
//! │  let clock = VirtualClock::new(...);                   │
//! │  clock.schedule(100, event);                           │
//! └────────────────────────────────────────────────────────┘
//!                      │
//!          ┌───────────┴───────────┐
//!          │                       │
//!   Production                 Verification
//!   (Runtime)                  (Kani)
//!          │                       │
//!   VirtualClock<               VirtualClock<
//!     ProductionBackend>          VerificationBackend>
//!          │                       │
//!   BinaryHeap + RwLock     [Option<Event>; 4] + RefCell
//!   (thread-safe,           (stack-only,
//!    heap-allocated)         Kani-friendly)
//! ```
//!
//! # TLA+ Specification
//! All implementations maintain the invariants from `specs/tla/VirtualClock.tla`
//!
//! # Physical Laws Enforced
//! - **T-001**: Time Monotonicity - Time never decreases
//! - **T-002**: Event Causality - Lamport ordering preserved
//! - **T-003**: Event Ordering - Events fire in total order

mod types;
mod backend;
mod production_backend;
mod verification_backend;
mod engine;

#[cfg(kani)]
mod proofs;

// Re-exports
pub use types::{
    EventId,
    EventPayload,
    LamportClock,
    ScheduledEvent,
    TimeMode,
    VirtualTimeNs,
};

pub use backend::ClockBackend;
pub use production_backend::ProductionBackend;
pub use verification_backend::VerificationBackend;
pub use engine::VirtualClock;

// Convenience type aliases
/// Production clock (thread-safe, heap-allocated)
pub type ProductionClock = VirtualClock<ProductionBackend>;

/// Verification clock (stack-only, Kani-friendly)
pub type VerificationClock = VirtualClock<VerificationBackend>;