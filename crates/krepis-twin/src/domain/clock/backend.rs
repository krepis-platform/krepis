//! Clock Backend Abstraction Layer
//!
//! # The Zero-cost Razor Architecture
//!
//! This module implements a trait-based backend system that allows us to swap
//! between production (heap-allocated, thread-safe) and verification (stack-allocated,
//! Kani-friendly) implementations at **compile time** with zero runtime overhead.
//!
//! # TLA+ Correspondence
//! The backend trait maps to the TLA+ state variables:
//! - `virtualTimeNs` → `current_time()`
//! - `lamportClock` → `current_lamport()`
//! - `eventQueue` → `push_event()`, `pop_event()`

use super::types::{LamportClock, ScheduledEvent, VirtualTimeNs};

/// Backend abstraction for clock state management
///
/// # Design Philosophy
/// This trait enables **Static Dispatch** - the concrete backend type is known
/// at compile time, allowing the compiler to:
/// 1. Inline all method calls
/// 2. Eliminate vtable lookups
/// 3. Optimize away abstraction overhead
///
/// # TLA+ Mapping
/// ```tla
/// VARIABLES virtualTimeNs, lamportClock, eventQueue
/// ```
pub trait ClockBackend {
    /// Get current virtual time
    ///
    /// # TLA+ Correspondence
    /// Returns the current value of `virtualTimeNs`
    fn current_time(&self) -> VirtualTimeNs;

    /// Get current Lamport clock
    ///
    /// # TLA+ Correspondence
    /// Returns the current value of `lamportClock`
    fn current_lamport(&self) -> LamportClock;

    /// Set virtual time (for tick operation)
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// virtualTimeNs' = nextEvent.time
    /// ```
    fn set_time(&mut self, time: VirtualTimeNs);

    /// Increment Lamport clock
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// lamportClock' = lamportClock + 1
    /// ```
    fn increment_lamport(&mut self) -> LamportClock;

    /// Reset Lamport clock (when queue becomes empty)
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// lamportClock' = IF eventQueue' = {} THEN 0 ELSE lamportClock
    /// ```
    fn reset_lamport(&mut self);

    /// Add event to queue
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// eventQueue' = eventQueue \cup {newEvent}
    /// ```
    ///
    /// # Returns
    /// `true` if event was added successfully
    fn push_event(&mut self, event: ScheduledEvent) -> bool;

    /// Remove and return next event (earliest by time, then Lamport)
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// CHOOSE e \in eventQueue :
    ///     \A other \in eventQueue :
    ///         \/ e.time < other.time
    ///         \/ (e.time = other.time /\ e.lamport <= other.lamport)
    /// ```
    fn pop_event(&mut self) -> Option<ScheduledEvent>;

    /// Check if event queue is empty
    fn is_empty(&self) -> bool;

    /// Get queue size
    fn queue_len(&self) -> usize;

    /// Reset to initial state
    ///
    /// # TLA+ Correspondence
    /// Returns to `Init` state:
    /// ```tla
    /// Init ==
    ///     /\ virtualTimeNs = 0
    ///     /\ lamportClock = 0
    ///     /\ eventQueue = {}
    /// ```
    fn reset(&mut self);
}