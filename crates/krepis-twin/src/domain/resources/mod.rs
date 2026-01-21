//! Resource Tracking & Deadlock Detection
//!
//! # Architecture
//!
//! This module implements the ResourceOracle from TLA+ specification.
//!
//! ## Zero-Cost Abstraction
//!
//! - **Production** (`#[cfg(not(feature = "twin"))]`): NoOpTracker
//!   - All methods are `#[inline(always)]` with empty bodies
//!   - Compiler optimizes away completely (zero runtime cost)
//!
//! - **Verification** (`#[cfg(feature = "twin")]`): DetailedTracker
//!   - Full wait-for graph tracking
//!   - Cycle detection (deadlock detection)
//!   - Heuristic metrics for Ki-DPOR
//!
//! ## TLA+ Correspondence
//!
//! ```tla
//! VARIABLES
//!     resources         -> DetailedTracker::resources
//!     waiting_queues    -> DetailedTracker::waiting_queues
//!     wait_for_graph    -> DetailedTracker::wait_for_graph
//!     thread_status     -> DetailedTracker::thread_status
//!
//! ACTIONS
//!     RequestResource   -> ResourceTracker::request
//!     ReleaseResource   -> ResourceTracker::release
//!     Finish            -> ResourceTracker::on_finish
//! ```

pub mod types;
pub mod tracker;

#[cfg(not(feature = "twin"))]
pub mod noop;

#[cfg(feature = "twin")]
pub mod detailed;

#[cfg(all(kani, feature = "twin"))]
pub mod proof;

// Re-exports
pub use types::*;
pub use tracker::{ResourceTracker, RequestResult};

#[cfg(not(feature = "twin"))]
pub use noop::NoOpTracker as DefaultTracker;

#[cfg(feature = "twin")]
pub use detailed::DetailedTracker as DefaultTracker;