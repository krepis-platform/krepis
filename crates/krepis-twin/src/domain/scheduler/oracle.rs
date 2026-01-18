//! SchedulerOracle - Thread-Aware Event Scheduling
//!
//! # Overview
//!
//! The SchedulerOracle combines VirtualClock (time and event management) with
//! thread state management to implement the complete scheduling algorithm
//! specified in `specs/tla/SchedulerOracle.tla`.
//!
//! # Architecture
//!
//! ```text
//! SchedulerOracle<SB, CB>
//!   ├─ scheduler_backend: SB     (thread states)
//!   ├─ clock: VirtualClock<CB>   (time and events)
//!   ├─ strategy: SchedulingStrategy
//!   └─ event_to_thread: HashMap<EventId, ThreadId>  (event ownership)
//! ```
//!
//! # TLA+ Correspondence
//!
//! This implementation directly corresponds to the TLA+ specification:
//!
//! ```tla
//! VARIABLES virtualTimeNs, lamportClock, eventQueue, threadStates
//!
//! Init ==
//!     /\ virtualTimeNs = 0
//!     /\ lamportClock = 0
//!     /\ eventQueue = {}
//!     /\ threadStates = [t \in Threads |-> "RUNNABLE"]
//!
//! ScheduleEvent(thread, delay) ==
//!     /\ virtualTimeNs + delay <= MaxTimeNs
//!     /\ Cardinality(eventQueue) < MaxEvents
//!     /\ thread \in Threads
//!     /\ LET newEvent = ...
//!        IN eventQueue' = eventQueue \cup {newEvent}
//!
//! ExecuteNext ==
//!     \/ ExecuteNext_Production
//!     \/ ExecuteNext_Verification
//! ```

use super::backend::SchedulerBackend;
use super::types::{SchedulerError, SchedulingStrategy, TaskId, ThreadId, ThreadState};
use crate::domain::clock::{ClockBackend, EventId, EventPayload, VirtualClock, VirtualTimeNs};

/// SchedulerOracle - The main scheduler implementation
///
/// # Type Parameters
///
/// - `SB`: SchedulerBackend (ProductionBackend or VerificationBackend)
/// - `CB`: ClockBackend (ProductionBackend or VerificationBackend)
///
/// # Monomorphization
///
/// When you instantiate `SchedulerOracle<ProductionSchedulerBackend, ProductionClockBackend>`,
/// the compiler generates a completely specialized version with:
/// - DashMap for thread states
/// - BinaryHeap for event queue
/// - Deterministic scheduling strategy
/// - All methods inlined
///
/// When you instantiate `SchedulerOracle<VerificationSchedulerBackend, VerificationClockBackend>`,
/// the compiler generates a different specialized version with:
/// - Fixed array for thread states
/// - Fixed array for event queue
/// - Non-deterministic scheduling (for Kani)
/// - All methods inlined
///
/// # Example
///
/// ```rust
/// use krepis_twin::domain::scheduler::{ProductionScheduler, ThreadId, SchedulingStrategy};
/// use krepis_twin::domain::clock::{ProductionBackend as ClockBackend, VirtualClock, TimeMode, EventPayload};
///
/// // Create clock
/// let clock_backend = ClockBackend::new();
/// let clock = VirtualClock::new(clock_backend, TimeMode::EventDriven);
///
/// // Create scheduler with 4 threads
/// let mut scheduler = ProductionScheduler::new(clock, 4, SchedulingStrategy::Production);
///
/// // Schedule task for thread 0
/// let task_id = scheduler.schedule_task(
///     ThreadId::new(0),
///     100,  // delay_ns
///     EventPayload::MemoryWriteSync { core: 0, addr: 0x1000, value: 42 }
/// ).unwrap();
///
/// // Execute the scheduled task
/// let executed = scheduler.execute_next().unwrap();
/// ```
pub struct SchedulerOracle<SB: SchedulerBackend, CB: ClockBackend> {
    /// Backend for thread state management
    scheduler_backend: SB,

    /// Virtual clock for time and event management
    clock: VirtualClock<CB>,

    /// Scheduling strategy (PRODUCTION or VERIFICATION)
    /// 
    /// Currently stored for future use in Phase 1B when we implement
    /// non-deterministic scheduling for verification mode.
    #[allow(dead_code)]
    strategy: SchedulingStrategy,

    /// Next task ID allocator
    next_task_id: TaskId,
}

impl<SB: SchedulerBackend, CB: ClockBackend> SchedulerOracle<SB, CB> {
    /// Create a new SchedulerOracle
    ///
    /// # Arguments
    ///
    /// - `clock`: VirtualClock for time and event management
    /// - `num_threads`: Number of threads to support
    /// - `strategy`: PRODUCTION (deterministic) or VERIFICATION (non-deterministic)
    ///
    /// # TLA+ Correspondence
    ///
    /// ```tla
    /// Init ==
    ///     /\ virtualTimeNs = 0
    ///     /\ lamportClock = 0
    ///     /\ eventQueue = {}
    ///     /\ threadStates = [t \in Threads |-> "RUNNABLE"]
    /// ```
    ///
    /// # Example
    ///
    /// ```rust
    /// use krepis_twin::domain::scheduler::{ProductionScheduler, SchedulingStrategy};
    /// use krepis_twin::domain::clock::{ProductionBackend, VirtualClock, TimeMode};
    ///
    /// let clock_backend = ProductionBackend::new();
    /// let clock = VirtualClock::new(clock_backend, TimeMode::EventDriven);
    /// let scheduler = ProductionScheduler::new(clock, 8, SchedulingStrategy::Production);
    /// ```
    pub fn new(clock: VirtualClock<CB>, num_threads: usize, strategy: SchedulingStrategy) -> Self {
        let scheduler_backend = SB::new(num_threads);

        Self {
            scheduler_backend,
            clock,
            strategy,
            next_task_id: TaskId::new(0),
        }
    }

    /// Get reference to the clock
    pub fn clock(&self) -> &VirtualClock<CB> {
        &self.clock
    }

    /// Get mutable reference to the clock
    pub fn clock_mut(&mut self) -> &mut VirtualClock<CB> {
        &mut self.clock
    }

    /// Get reference to the scheduler backend
    pub fn backend(&self) -> &SB {
        &self.scheduler_backend
    }

    /// Get current virtual time
    #[inline(always)]
    pub fn now_ns(&self) -> VirtualTimeNs {
        self.clock.now_ns()
    }

    /// Get current Lamport clock
    #[inline(always)]
    pub fn lamport(&self) -> u64 {
        self.clock.lamport()
    }

    /// Get number of pending events
    pub fn pending_events(&self) -> usize {
        self.clock.pending_events()
    }

    /// Get thread state
    pub fn get_thread_state(&self, thread_id: ThreadId) -> Result<ThreadState, SchedulerError> {
        self.scheduler_backend.get_state(thread_id)
    }

    /// Set thread state
    ///
    /// # State Transitions
    ///
    /// Valid transitions:
    /// - RUNNABLE -> BLOCKED (thread waits for resource)
    /// - BLOCKED -> RUNNABLE (resource becomes available)
    /// - RUNNABLE -> COMPLETED (thread finishes)
    ///
    /// Invalid transitions (not enforced yet, but semantically wrong):
    /// - COMPLETED -> anything (completed is terminal)
    ///
    /// # Example
    ///
    /// ```rust
    /// use krepis_twin::domain::scheduler::{ProductionScheduler, ThreadId, ThreadState, SchedulingStrategy};
    /// use krepis_twin::domain::clock::{ProductionBackend, VirtualClock, TimeMode};
    ///
    /// let clock = VirtualClock::new(ProductionBackend::new(), TimeMode::EventDriven);
    /// let mut scheduler = ProductionScheduler::new(clock, 4, SchedulingStrategy::Production);
    ///
    /// // Block thread 0
    /// scheduler.set_thread_state(ThreadId::new(0), ThreadState::Blocked).unwrap();
    ///
    /// // Unblock it later
    /// scheduler.set_thread_state(ThreadId::new(0), ThreadState::Runnable).unwrap();
    /// ```
    pub fn set_thread_state(
        &mut self,
        thread_id: ThreadId,
        new_state: ThreadState,
    ) -> Result<ThreadState, SchedulerError> {
        self.scheduler_backend.set_state(thread_id, new_state)
    }

    /// Schedule a task for execution
    ///
    /// # TLA+ Correspondence
    ///
    /// ```tla
    /// ScheduleEvent(thread, delay) ==
    ///     /\ virtualTimeNs + delay <= MaxTimeNs
    ///     /\ Cardinality(eventQueue) < MaxEvents
    ///     /\ thread \in Threads
    ///     /\ threadStates[thread] = "RUNNABLE"
    ///     /\ LET newLamport == lamportClock + 1
    ///            newEventId == Cardinality(eventQueue) + 1
    ///            newEvent == CreateEvent(virtualTimeNs + delay, newLamport, newEventId, thread)
    ///        IN  /\ eventQueue' = eventQueue \cup {newEvent}
    ///            /\ lamportClock' = newLamport
    ///            /\ UNCHANGED <<virtualTimeNs, threadStates>>
    /// ```
    ///
    /// # Arguments
    ///
    /// - `thread_id`: Which thread this task belongs to
    /// - `delay_ns`: When to execute (nanoseconds from now)
    /// - `payload`: What to execute
    ///
    /// # Returns
    ///
    /// `TaskId` that can be used to track this task
    ///
    /// # Errors
    ///
    /// - `InvalidThreadId`: Thread ID out of bounds
    /// - `InvalidThreadState`: Thread is not RUNNABLE
    /// - `TimeOverflow`: delay_ns would overflow time
    /// - `QueueFull`: Event queue is full
    ///
    /// # Example
    ///
    /// ```rust
    /// use krepis_twin::domain::scheduler::{ProductionScheduler, ThreadId, SchedulingStrategy};
    /// use krepis_twin::domain::clock::{ProductionBackend, VirtualClock, TimeMode, EventPayload};
    ///
    /// let clock = VirtualClock::new(ProductionBackend::new(), TimeMode::EventDriven);
    /// let mut scheduler = ProductionScheduler::new(clock, 4, SchedulingStrategy::Production);
    ///
    /// // Schedule memory write for thread 0
    /// let task = scheduler.schedule_task(
    ///     ThreadId::new(0),
    ///     100,
    ///     EventPayload::MemoryWriteSync { core: 0, addr: 0x1000, value: 42 }
    /// ).unwrap();
    /// ```
    pub fn schedule_task(
        &mut self,
        thread_id: ThreadId,
        delay_ns: VirtualTimeNs,
        payload: EventPayload,
    ) -> Result<TaskId, SchedulerError> {
        // Precondition 1: Thread must exist
        let thread_state = self.scheduler_backend.get_state(thread_id)?;

        // Precondition 2: Thread must be RUNNABLE
        // (In Phase 1A we allow scheduling for any state, but in Phase 1B
        // we might want to enforce this more strictly)
        if !thread_state.is_runnable() {
            return Err(SchedulerError::InvalidThreadState {
                thread_id,
                current_state: thread_state,
                expected_state: ThreadState::Runnable,
            });
        }

        // Schedule event in the clock
        let event_id = self.clock.schedule(delay_ns, payload)
            .ok_or_else(|| SchedulerError::TimeOverflow {
                current_time_ns: self.clock.now_ns(),
                delay_ns,
                max_time_ns: u64::MAX,
            })?;

        // Record event ownership
        self.scheduler_backend.register_event(event_id, thread_id)?;

        // Allocate task ID
        let task_id = self.next_task_id;
        self.next_task_id = TaskId::new(self.next_task_id.as_usize() + 1);

        Ok(task_id)
    }

    /// Execute the next runnable event
    ///
    /// # TLA+ Correspondence
    ///
    /// ## PRODUCTION Mode
    ///
    /// ```tla
    /// ExecuteNext_Production ==
    ///     /\ Strategy = "PRODUCTION"
    ///     /\ RunnableEvents /= {}
    ///     /\ LET nextEvent == CHOOSE e \in RunnableEvents :
    ///                             \A other \in RunnableEvents :
    ///                                 \/ e.time < other.time
    ///                                 \/ (e.time = other.time /\ e.lamport < other.lamport)
    ///                                 \/ (e.time = other.time /\ e.lamport = other.lamport
    ///                                     /\ e.eventId <= other.eventId)
    ///        IN  /\ virtualTimeNs' = nextEvent.time
    ///            /\ eventQueue' = eventQueue \ {nextEvent}
    ///            /\ UNCHANGED <<lamportClock, threadStates>>
    /// ```
    ///
    /// ## VERIFICATION Mode
    ///
    /// ```tla
    /// ExecuteNext_Verification ==
    ///     /\ Strategy = "VERIFICATION"
    ///     /\ RunnableEvents /= {}
    ///     /\ \E nextEvent \in RunnableEvents :
    ///            /\ virtualTimeNs' = nextEvent.time
    ///            /\ eventQueue' = eventQueue \ {nextEvent}
    ///            /\ UNCHANGED <<lamportClock, threadStates>>
    /// ```
    ///
    /// # Algorithm
    ///
    /// 1. Get next event from clock (via `tick()`)
    /// 2. Check if event's thread is RUNNABLE
    /// 3. If yes, execute it; if no, skip it and try next event
    /// 4. Repeat until a runnable event is found or queue is empty
    ///
    /// # Returns
    ///
    /// - `Ok(Some(event_id))`: An event was executed
    /// - `Ok(None)`: No runnable events (all threads blocked or completed)
    /// - `Err(...)`: An error occurred
    ///
    /// # Example
    ///
    /// ```rust
    /// use krepis_twin::domain::scheduler::{ProductionScheduler, ThreadId, SchedulingStrategy};
    /// use krepis_twin::domain::clock::{ProductionBackend, VirtualClock, TimeMode, EventPayload};
    ///
    /// let clock = VirtualClock::new(ProductionBackend::new(), TimeMode::EventDriven);
    /// let mut scheduler = ProductionScheduler::new(clock, 4, SchedulingStrategy::Production);
    ///
    /// // Schedule something
    /// scheduler.schedule_task(
    ///     ThreadId::new(0),
    ///     100,
    ///     EventPayload::MemoryWriteSync { core: 0, addr: 0x1000, value: 42 }
    /// ).unwrap();
    ///
    /// // Execute it
    /// let result = scheduler.execute_next().unwrap();
    /// assert!(result.is_some());
    /// ```
    pub fn execute_next(&mut self) -> Result<Option<EventId>, SchedulerError> {
        // Keep trying until we find a runnable event or run out of events
        loop {
            // Get next event from clock
            let Some(event) = self.clock.tick() else {
                // No more events
                return Ok(None);
            };

            // Look up which thread owns this event
            let Some(thread_id) = self.scheduler_backend.get_event_owner(event.event_id) else {
                continue;
            };

            // Check if thread is runnable
            if !self.scheduler_backend.is_runnable(thread_id) {
                // Thread is BLOCKED or COMPLETED, skip this event
                continue;
            }

            // Thread is RUNNABLE, execute the event
            // (In Phase 1A, we just consume the event. In future phases,
            // we might dispatch to actual handlers based on payload)
            
            // Clean up ownership tracking
            self.scheduler_backend.unregister_event(event.event_id);

            return Ok(Some(event.event_id));
        }
    }

    /// Execute all pending runnable events
    ///
    /// This is a convenience method that repeatedly calls `execute_next()`
    /// until no more runnable events remain.
    ///
    /// # Returns
    ///
    /// Number of events executed
    ///
    /// # Example
    ///
    /// ```rust
    /// use krepis_twin::domain::scheduler::{ProductionScheduler, ThreadId, SchedulingStrategy};
    /// use krepis_twin::domain::clock::{ProductionBackend, VirtualClock, TimeMode, EventPayload};
    ///
    /// let clock = VirtualClock::new(ProductionBackend::new(), TimeMode::EventDriven);
    /// let mut scheduler = ProductionScheduler::new(clock, 4, SchedulingStrategy::Production);
    ///
    /// // Schedule multiple tasks
    /// scheduler.schedule_task(ThreadId::new(0), 100, EventPayload::MemoryWriteSync { core: 0, addr: 0, value: 1 }).unwrap();
    /// scheduler.schedule_task(ThreadId::new(1), 200, EventPayload::MemoryWriteSync { core: 0, addr: 1, value: 2 }).unwrap();
    /// scheduler.schedule_task(ThreadId::new(2), 300, EventPayload::MemoryWriteSync { core: 0, addr: 2, value: 3 }).unwrap();
    ///
    /// // Execute all
    /// let count = scheduler.execute_all().unwrap();
    /// assert_eq!(count, 3);
    /// ```
    pub fn execute_all(&mut self) -> Result<usize, SchedulerError> {
        let mut count = 0;
        
        while self.execute_next()?.is_some() {
            count += 1;
            
            // Safety limit to prevent infinite loops in case of bugs
            if count > 100_000 {
                break;
            }
        }
        
        Ok(count)
    }

    /// Check if scheduler is idle (no runnable events)
    ///
    /// This returns `true` if either:
    /// - The event queue is empty
    /// - All events belong to non-runnable threads
    pub fn is_idle(&self) -> bool {
        self.clock.is_idle() || self.count_runnable_events() == 0
    }

    /// Count how many events belong to runnable threads
    ///
    /// This is useful for diagnostics and deadlock detection.
    pub fn count_runnable_events(&self) -> usize {
        self.scheduler_backend.count_runnable_events()
    }

    /// Get thread state statistics
    ///
    /// Returns `(runnable_count, blocked_count, completed_count)`
    pub fn thread_state_counts(&self) -> (usize, usize, usize) {
        self.scheduler_backend.state_counts()
    }

    /// Reset scheduler to initial state
    ///
    /// # TLA+ Correspondence
    ///
    /// Returns to `Init` state
    pub fn reset(&mut self) {
        self.clock.reset();
        self.scheduler_backend.reset();
        self.scheduler_backend.clear_events();
        self.next_task_id = TaskId::new(0);
    }
}

#[cfg(all(test, not(kani)))]
mod tests {
    use super::*;
    use crate::domain::clock::{ProductionBackend as ProdClockBackend, TimeMode};
    use crate::domain::scheduler::production_backend::ProductionBackend as ProdSchedBackend;

    type TestScheduler = SchedulerOracle<ProdSchedBackend, ProdClockBackend>;

    #[test]
    fn test_scheduler_creation() {
        let clock = VirtualClock::new(ProdClockBackend::new(), TimeMode::EventDriven);
        let scheduler = TestScheduler::new(clock, 4, SchedulingStrategy::Production);

        assert_eq!(scheduler.now_ns(), 0);
        assert_eq!(scheduler.lamport(), 0);
        assert_eq!(scheduler.pending_events(), 0);
    }

    #[test]
    fn test_schedule_and_execute() {
        let clock = VirtualClock::new(ProdClockBackend::new(), TimeMode::EventDriven);
        let mut scheduler = TestScheduler::new(clock, 4, SchedulingStrategy::Production);

        // Schedule a task
        let task_id = scheduler
            .schedule_task(
                ThreadId::new(0),
                100,
                EventPayload::MemoryWriteSync {
                    core: 0,
                    addr: 0x1000,
                    value: 42,
                },
            )
            .unwrap();

        assert!(task_id.as_usize() == 0); // First task
        assert_eq!(scheduler.pending_events(), 1);

        // Execute it
        let result = scheduler.execute_next().unwrap();
        assert!(result.is_some());
        assert_eq!(scheduler.pending_events(), 0);
    }

    #[test]
    fn test_blocked_thread_not_executed() {
        let clock = VirtualClock::new(ProdClockBackend::new(), TimeMode::EventDriven);
        let mut scheduler = TestScheduler::new(clock, 4, SchedulingStrategy::Production);

        // Block thread 0
        scheduler
            .set_thread_state(ThreadId::new(0), ThreadState::Blocked)
            .unwrap();

        // Try to schedule for blocked thread (should fail)
        let result = scheduler.schedule_task(
            ThreadId::new(0),
            100,
            EventPayload::MemoryWriteSync {
                core: 0,
                addr: 0x1000,
                value: 42,
            },
        );

        assert!(result.is_err());
    }

    #[test]
    fn test_multiple_threads() {
        let clock = VirtualClock::new(ProdClockBackend::new(), TimeMode::EventDriven);
        let mut scheduler = TestScheduler::new(clock, 4, SchedulingStrategy::Production);

        // Schedule tasks for different threads
        scheduler
            .schedule_task(
                ThreadId::new(0),
                100,
                EventPayload::MemoryWriteSync {
                    core: 0,
                    addr: 0,
                    value: 1,
                },
            )
            .unwrap();

        scheduler
            .schedule_task(
                ThreadId::new(1),
                50, // Earlier time
                EventPayload::MemoryWriteSync {
                    core: 0,
                    addr: 1,
                    value: 2,
                },
            )
            .unwrap();

        assert_eq!(scheduler.pending_events(), 2);

        // Execute all
        let count = scheduler.execute_all().unwrap();
        assert_eq!(count, 2);
        assert_eq!(scheduler.pending_events(), 0);
    }

    #[test]
    fn test_execute_all() {
        let clock = VirtualClock::new(ProdClockBackend::new(), TimeMode::EventDriven);
        let mut scheduler = TestScheduler::new(clock, 4, SchedulingStrategy::Production);

        // Schedule 5 tasks
        for i in 0..5 {
            scheduler
                .schedule_task(
                    ThreadId::new(i % 4),
                    ((i + 1) * 100).try_into().unwrap(),
                    EventPayload::MemoryWriteSync {
                        core: i % 4,
                        addr: i as usize,
                        value: i as u64,
                    },
                )
                .unwrap();
        }

        assert_eq!(scheduler.pending_events(), 5);

        let count = scheduler.execute_all().unwrap();
        assert_eq!(count, 5);
        assert!(scheduler.is_idle());
    }
}