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
//! │ DporScheduler   │
//! ├─────────────────┤
//! │ - stack         │  Execution trace
//! │ - backtrack_sets│  Threads to explore at each depth
//! │ - done_sets     │  Already explored threads
//! │ - clock_vectors │  Causality tracking
//! └─────────────────┘
//!         │
//!         ├─→ VectorClock (happens-before)
//!         └─→ ResourceTracker (dependency detection)
//! ```
//!
//! # Feature Gating
//!
//! This entire module is only compiled with `--features twin`.
//! Production builds have zero overhead.

#![cfg(feature = "twin")]

pub mod vector_clock;
pub mod scheduler;

#[cfg(kani)]
pub mod proof;

// Re-exports
pub use vector_clock::VectorClock;
pub use scheduler::{DporScheduler, StepRecord, Operation, DporStats};

/// Maximum threads supported by DPOR
pub const MAX_THREADS: usize = 8;

/// Maximum exploration depth
pub const MAX_DEPTH: usize = 20;