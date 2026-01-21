//! Classic DPOR (Dynamic Partial Order Reduction)
//!
//! # Overview
//!
//! This module implements the Classic DPOR algorithm for efficient state space
//! exploration of concurrent programs. Instead of exploring all possible thread
//! interleavings (exponential complexity), DPOR only explores representative
//! interleavings from each equivalence class.
//!
//! # Key Insight
//!
//! Two execution traces are equivalent if they differ only in the order of
//! INDEPENDENT operations. DPOR identifies and skips equivalent traces.
//!
//! # Reduction
//!
//! For N threads with M operations each:
//! - Full exploration: O((N*M)!) states
//! - DPOR: O(|Dependent Ops| * Depth) states
//! - Typical reduction: 10x-100x fewer states
//!
//! # Architecture
//!
//! ```text
//! ┌─────────────────┐
//! │ DporScheduler   │  (Classic - Stack-based DFS)
//! ├─────────────────┤
//! │ - stack         │  Execution trace
//! │ - backtrack_sets│  Threads to explore at each depth
//! │ - done_sets     │  Already explored threads
//! │ - clock_vectors │  Causality tracking
//! └─────────────────┘
//!
//! ┌─────────────────┐
//! │ KiDporScheduler │  (Intelligent - Priority Queue A*)
//! ├─────────────────┤
//! │ - open_set      │  Priority queue of states
//! │ - explored_set  │  Visited state signatures
//! │ - heuristic     │  Danger-based prioritization
//! └─────────────────┘
//! ```
//!
//! # Feature Gating
//!
//! This entire module is only compiled with `--features twin`.
//! Production builds have zero overhead.

#![cfg(feature = "twin")]

pub mod vector_clock;
pub mod scheduler;

// Ki-DPOR (A* based)
pub mod ki_state;
pub mod ki_scheduler;

#[cfg(kani)]
pub mod proof;

// Re-exports
pub use vector_clock::VectorClock;
pub use scheduler::{DporScheduler, StepRecord, Operation, DporStats, TinyBitSet};

// Ki-DPOR exports
pub use ki_state::{KiState, ThreadStatus};
pub use ki_scheduler::{KiDporScheduler, LivenessViolation, MAX_STARVATION_LIMIT};

/// Maximum threads supported by DPOR
pub const MAX_THREADS: usize = 8;

/// Maximum exploration depth
pub const MAX_DEPTH: usize = 20;