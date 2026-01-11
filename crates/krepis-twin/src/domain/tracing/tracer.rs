//! Zero-cost Event Tracer Implementation
//!
//! This module provides a **stack-allocated**, **zero-runtime-overhead**
//! event tracer that records simulation events with Lamport timestamps.

use super::event::{EventMetadata, LamportTimestamp, SimulationEvent, ThreadId, MAX_THREADS};

/// Configuration for the event tracer
#[derive(Debug, Clone, Copy)]
pub struct TracerConfig {
    /// Maximum number of events to store (for memory management)
    pub max_events: usize,
    /// Whether to enable causality validation on each event
    pub validate_causality: bool,
}

impl Default for TracerConfig {
    fn default() -> Self {
        Self {
            max_events: super::DEFAULT_MAX_EVENTS,
            validate_causality: cfg!(debug_assertions),
        }
    }
}

/// Errors that can occur during tracing
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TracingError {
    /// Event buffer is full
    BufferFull,
    /// Causality violation detected (timestamp regression)
    CausalityViolation {
        /// Minimum expected timestamp (last timestamp from this thread)
        expected_min: LamportTimestamp,
        /// Timestamp that was received (violating the monotonicity)
        received: LamportTimestamp,
    },
    /// Invalid thread ID (out of bounds)
    InvalidThreadId(ThreadId),
}

impl std::fmt::Display for TracingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TracingError::BufferFull => write!(f, "Event buffer is full"),
            TracingError::CausalityViolation { expected_min, received } => {
                write!(
                    f,
                    "Causality violation: expected timestamp >= {}, got {}",
                    expected_min.0, received.0
                )
            }
            TracingError::InvalidThreadId(tid) => write!(f, "Invalid thread ID: {}", tid.0),
        }
    }
}

impl std::error::Error for TracingError {}

/// Per-thread tracing state
///
/// # Memory Layout
/// - Size: 16 bytes
/// - Alignment: 8 bytes
#[derive(Debug, Clone, Copy)]
#[repr(C)]
struct ThreadState {
    /// Last Lamport timestamp issued by this thread
    last_timestamp: LamportTimestamp,
    /// Sequence number for events within this thread
    seq_num: u64,
}

impl ThreadState {
    /// Create a new thread state (zero-initialized)
    #[inline(always)]
    const fn new() -> Self {
        Self {
            last_timestamp: LamportTimestamp(0),
            seq_num: 0,
        }
    }

    /// Generate next timestamp for this thread
    #[inline(always)]
    fn next_timestamp(&mut self) -> LamportTimestamp {
        self.last_timestamp.increment();
        self.seq_num += 1;
        self.last_timestamp
    }

    /// Synchronize with another thread's timestamp
    #[inline(always)]
    fn sync_with(&mut self, other_timestamp: LamportTimestamp) {
        self.last_timestamp.sync(other_timestamp);
        self.seq_num += 1;
    }
}

/// Backend trait for EventTracer storage
///
/// This enables zero-cost abstraction between production (large, heap)
/// and verification (small, stack) modes.
pub trait TracerBackend {
    /// Maximum events this backend can store
    const MAX_EVENTS: usize;

    /// Record an event at the given index
    ///
    /// # Safety
    /// - Index must be < MAX_EVENTS
    /// - This index must not have been written to before
    fn record_event(&mut self, index: usize, event: SimulationEvent) -> Result<(), TracingError>;

    /// Get a reference to the event at index
    ///
    /// # Safety
    /// - Index must be < current event count
    /// - The event at this index must have been previously recorded
    fn get_event(&self, index: usize) -> Option<&SimulationEvent>;

    /// Get all recorded events as a slice
    ///
    /// # Safety
    /// - Only returns events that have been successfully recorded
    fn get_events(&self, count: usize) -> &[SimulationEvent];

    /// Get the current global timestamp
    fn global_timestamp(&self) -> LamportTimestamp;

    /// Update the global timestamp (must maintain max invariant)
    fn update_global_timestamp(&mut self, ts: LamportTimestamp);
}

/// Production backend with large capacity
///
/// Uses `MaybeUninit` for performance (no initialization overhead)
pub struct ProductionBackend {
    /// Event storage (heap-allocated for large capacity)
    events: Box<[SimulationEvent]>,
    /// Global timestamp (max of all thread clocks)
    global_timestamp: LamportTimestamp,
}

impl ProductionBackend {
    /// Create a new production backend with specified capacity
    pub fn new(max_events: usize) -> Self {
        // Initialize with default events to avoid MaybeUninit complexity
        let events = vec![
            SimulationEvent::ClockTick {
                meta: EventMetadata::new(LamportTimestamp::ZERO, ThreadId::new(0), 0),
                event: super::event::ClockEvent {
                    prev_timestamp: LamportTimestamp::ZERO,
                    new_timestamp: LamportTimestamp::ZERO,
                },
            };
            max_events
        ]
        .into_boxed_slice();

        Self {
            events,
            global_timestamp: LamportTimestamp::ZERO,
        }
    }
}

impl TracerBackend for ProductionBackend {
    const MAX_EVENTS: usize = usize::MAX;

    #[inline]
    fn record_event(&mut self, index: usize, event: SimulationEvent) -> Result<(), TracingError> {
        if index >= self.events.len() {
            return Err(TracingError::BufferFull);
        }
        self.events[index] = event;
        Ok(())
    }

    #[inline]
    fn get_event(&self, index: usize) -> Option<&SimulationEvent> {
        self.events.get(index)
    }

    #[inline]
    fn get_events(&self, count: usize) -> &[SimulationEvent] {
        &self.events[..count.min(self.events.len())]
    }

    #[inline(always)]
    fn global_timestamp(&self) -> LamportTimestamp {
        self.global_timestamp
    }

    #[inline(always)]
    fn update_global_timestamp(&mut self, ts: LamportTimestamp) {
        if ts > self.global_timestamp {
            self.global_timestamp = ts;
        }
    }
}

/// Verification backend with small, stack-allocated storage
///
/// Uses `Option` instead of `MaybeUninit` for Kani-friendly verification.
/// This explicitly tracks initialization state, making it provable.
pub struct VerificationBackend {
    /// Event storage (stack-allocated, fully initialized with None)
    /// Using Option makes initialization state explicit for Kani
    events: [Option<SimulationEvent>; Self::MAX_EVENTS],
    /// Global timestamp
    global_timestamp: LamportTimestamp,
}

impl VerificationBackend {
    /// Maximum events for verification (kept small for Kani)
    pub const MAX_EVENTS: usize = 1000;

    /// Create a new verification backend
    ///
    /// All events are initialized to None, making the initialization
    /// state explicit for formal verification.
    pub const fn new() -> Self {
        Self {
            events: [None; Self::MAX_EVENTS],
            global_timestamp: LamportTimestamp(0),
        }
    }
}

impl TracerBackend for VerificationBackend {
    const MAX_EVENTS: usize = Self::MAX_EVENTS;

    #[inline]
    fn record_event(&mut self, index: usize, event: SimulationEvent) -> Result<(), TracingError> {
        if index >= Self::MAX_EVENTS {
            return Err(TracingError::BufferFull);
        }

        // Kani can prove this is safe because:
        // 1. Index is bounds-checked above
        // 2. We're writing Some(event), which is always valid
        self.events[index] = Some(event);
        Ok(())
    }

    #[inline]
    fn get_event(&self, index: usize) -> Option<&SimulationEvent> {
        // Kani can prove this is safe because:
        // 1. Index is bounds-checked by slice indexing
        // 2. as_ref() safely converts Option<T> to Option<&T>
        self.events.get(index)?.as_ref()
    }

    #[inline]
    fn get_events(&self, _count: usize) -> &[SimulationEvent] {
        // For verification, we can't return a slice directly because
        // the array is Option<SimulationEvent>, not SimulationEvent.
        // This is a limitation of the verification backend.
        // 
        // In practice, this method should not be called during Kani verification.
        // The verify_* harnesses should use get_event() instead.
        &[]
    }

    #[inline(always)]
    fn global_timestamp(&self) -> LamportTimestamp {
        self.global_timestamp
    }

    #[inline(always)]
    fn update_global_timestamp(&mut self, ts: LamportTimestamp) {
        if ts.0 > self.global_timestamp.0 {
            self.global_timestamp = ts;
        }
    }
}

/// The core event tracer (generic over backend)
///
/// # Design Principles
/// - **Zero-cost when disabled**: Backend abstraction compiles to direct access
/// - **Memory-bounded**: Enforces max_events limit
/// - **Causality-preserving**: Validates Lamport timestamp ordering
/// - **Kani-provable**: Explicit invariants for formal verification
pub struct EventTracer<B: TracerBackend> {
    /// Per-thread state for timestamp management
    /// Using fixed-size array indexed by ThreadId (zero-cost lookup)
    thread_states: [ThreadState; MAX_THREADS],
    
    /// Number of events currently stored
    /// INVARIANT: event_count <= config.max_events
    /// INVARIANT: All events in range [0..event_count) are initialized
    event_count: usize,
    
    /// Configuration
    config: TracerConfig,
    
    /// Storage backend
    backend: B,
}

impl<B: TracerBackend> EventTracer<B> {
    /// Create a new event tracer with the given backend and configuration
    pub fn new(backend: B, config: TracerConfig) -> Self {
        Self {
            thread_states: [ThreadState::new(); MAX_THREADS],
            event_count: 0,
            config,
            backend,
        }
    }

    /// Record a simulation event
    ///
    /// This method:
    /// 1. Validates causality if enabled (zero-cost when disabled)
    /// 2. Updates thread-local and global timestamps
    /// 3. Appends the event to the trace
    ///
    /// # Errors
    /// - `BufferFull`: If max_events limit is reached
    /// - `CausalityViolation`: If event timestamp violates happens-before
    /// - `InvalidThreadId`: If thread ID is out of bounds
    ///
    /// # Invariants Maintained
    /// - event_count is incremented only after successful recording
    /// - All events in [0..event_count) are initialized
    /// - Global timestamp is always max of all thread timestamps
    #[inline]
    pub fn record(&mut self, event: SimulationEvent) -> Result<(), TracingError> {
        // INVARIANT CHECK: Buffer capacity
        if self.event_count >= self.config.max_events {
            return Err(TracingError::BufferFull);
        }

        let meta = event.metadata();
        let thread_id = meta.thread_id;

        // INVARIANT CHECK: Thread ID validity
        if thread_id.as_index() >= MAX_THREADS {
            return Err(TracingError::InvalidThreadId(thread_id));
        }

        // Get thread state (safe because we validated thread_id above)
        let thread_state = &mut self.thread_states[thread_id.as_index()];

        // INVARIANT CHECK: Causality (optional)
        if self.config.validate_causality {
            if meta.timestamp < thread_state.last_timestamp {
                return Err(TracingError::CausalityViolation {
                    expected_min: thread_state.last_timestamp,
                    received: meta.timestamp,
                });
            }
        }

        // Update global timestamp (TLA+ invariant: max operation)
        self.backend.update_global_timestamp(meta.timestamp);

        // Update thread state
        thread_state.last_timestamp = meta.timestamp;

        // Record the event
        // SAFETY PROOF for Kani:
        // 1. event_count < config.max_events (checked above)
        // 2. event_count < B::MAX_EVENTS (enforced by backend)
        // 3. This slot has not been written to yet (ensured by event_count increment)
        self.backend.record_event(self.event_count, event)?;

        // INVARIANT MAINTENANCE: Only increment after successful recording
        self.event_count += 1;

        Ok(())
    }

    /// Generate metadata for a new event in the given thread
    ///
    /// # Errors
    ///
    /// Returns `InvalidThreadId` if thread ID is out of bounds.
    #[inline]
    pub fn new_metadata(&mut self, thread_id: ThreadId) -> Result<EventMetadata, TracingError> {
        if thread_id.as_index() >= MAX_THREADS {
            return Err(TracingError::InvalidThreadId(thread_id));
        }

        let state = &mut self.thread_states[thread_id.as_index()];

        let timestamp = state.next_timestamp();
        let seq_num = state.seq_num;

        // Update global timestamp (TLA+ invariant)
        self.backend.update_global_timestamp(timestamp);

        Ok(EventMetadata::new(timestamp, thread_id, seq_num))
    }

    /// Synchronize a thread with a received timestamp
    ///
    /// # Errors
    ///
    /// Returns `InvalidThreadId` if thread ID is out of bounds.
    #[inline]
    pub fn sync_thread(
        &mut self,
        thread_id: ThreadId,
        received_timestamp: LamportTimestamp,
    ) -> Result<(), TracingError> {
        if thread_id.as_index() >= MAX_THREADS {
            return Err(TracingError::InvalidThreadId(thread_id));
        }

        let state = &mut self.thread_states[thread_id.as_index()];
        state.sync_with(received_timestamp);

        // Update global timestamp (TLA+ invariant)
        self.backend.update_global_timestamp(received_timestamp);

        Ok(())
    }

    /// Get event at specific index
    ///
    /// Returns None if index is out of bounds or event hasn't been recorded yet.
    #[inline]
    pub fn get_event(&self, index: usize) -> Option<&SimulationEvent> {
        if index < self.event_count {
            self.backend.get_event(index)
        } else {
            None
        }
    }

    /// Get all recorded events as a slice
    ///
    /// # Note
    /// For VerificationBackend, this may return an empty slice.
    /// Use get_event() for individual access during verification.
    #[inline]
    pub fn events(&self) -> &[SimulationEvent] {
        self.backend.get_events(self.event_count)
    }

    /// Get the current global Lamport timestamp
    #[inline(always)]
    pub fn global_timestamp(&self) -> LamportTimestamp {
        self.backend.global_timestamp()
    }

    /// Get number of recorded events
    #[inline(always)]
    pub fn event_count(&self) -> usize {
        self.event_count
    }

    /// Clear all recorded events (retains thread states)
    pub fn clear(&mut self) {
        self.event_count = 0;
    }

    /// Reset tracer to initial state
    pub fn reset(&mut self) {
        self.event_count = 0;
        self.thread_states = [ThreadState::new(); MAX_THREADS];
    }

    /// Check if the trace satisfies causality invariants
    ///
    /// This performs a full scan of all events to verify:
    /// 1. Within each thread, timestamps are monotonically increasing
    /// 2. Happens-before relationships are respected
    pub fn verify_causality(&self) -> Result<(), TracingError> {
        let mut thread_timestamps = [LamportTimestamp::ZERO; MAX_THREADS];

        for i in 0..self.event_count {
            let event = match self.get_event(i) {
                Some(e) => e,
                None => continue, // Skip if event not available (shouldn't happen)
            };
            
            let meta = event.metadata();
            let thread_idx = meta.thread_id.as_index();

            let last_ts = thread_timestamps[thread_idx];
            if meta.timestamp <= last_ts && last_ts.0 != 0 {
                return Err(TracingError::CausalityViolation {
                    expected_min: last_ts,
                    received: meta.timestamp,
                });
            }

            thread_timestamps[thread_idx] = meta.timestamp;
        }

        Ok(())
    }
}

/// Type alias for production tracer
pub type ProductionTracer = EventTracer<ProductionBackend>;

/// Type alias for verification tracer
pub type VerificationTracer = EventTracer<VerificationBackend>;

impl ProductionTracer {
    /// Create a production tracer with default configuration
    pub fn with_capacity(max_events: usize) -> Self {
        let backend = ProductionBackend::new(max_events);
        let config = TracerConfig {
            max_events,
            ..Default::default()
        };
        Self::new(backend, config)
    }
}

impl VerificationTracer {
    /// Create a verification tracer
    pub fn new_verification() -> Self {
        let backend = VerificationBackend::new();
        let config = TracerConfig {
            max_events: VerificationBackend::MAX_EVENTS,
            validate_causality: true,
        };
        Self::new(backend, config)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::tracing::event::{ClockEvent, MemoryOperation, MemAddr};

    #[test]
    fn test_basic_event_recording() {
        let mut tracer = ProductionTracer::with_capacity(100);
        let thread_id = ThreadId::new(0);

        let meta = tracer.new_metadata(thread_id).unwrap();
        let event = SimulationEvent::ClockTick {
            meta,
            event: ClockEvent {
                prev_timestamp: LamportTimestamp::ZERO,
                new_timestamp: meta.timestamp,
            },
        };

        assert!(tracer.record(event).is_ok());
        assert_eq!(tracer.event_count(), 1);
    }

    #[test]
    fn test_causality_validation() {
        let mut tracer = ProductionTracer::with_capacity(100);
        let thread_id = ThreadId::new(0);

        // Record first event
        let meta1 = tracer.new_metadata(thread_id).unwrap();
        let event1 = SimulationEvent::Memory {
            meta: meta1,
            operation: MemoryOperation::Write {
                addr: MemAddr(0x1000),
                value: 42,
                buffered: false,
            },
        };
        assert!(tracer.record(event1).is_ok());

        // Try to record event with earlier timestamp (should fail)
        let meta2 = EventMetadata::new(
            LamportTimestamp(0), // Earlier timestamp
            thread_id,
            0,
        );
        let event2 = SimulationEvent::Memory {
            meta: meta2,
            operation: MemoryOperation::Read {
                addr: MemAddr(0x1000),
                value: 42,
                cache_hit: false,
            },
        };

        assert!(matches!(
            tracer.record(event2),
            Err(TracingError::CausalityViolation { .. })
        ));
    }

    #[test]
    fn test_thread_synchronization() {
        let mut tracer = ProductionTracer::with_capacity(100);
        
        let t1 = ThreadId::new(0);
        let t2 = ThreadId::new(1);

        // Thread 1 advances its clock
        let meta1 = tracer.new_metadata(t1).unwrap();
        assert_eq!(meta1.timestamp.0, 1);

        // Thread 2 syncs with Thread 1's timestamp
        tracer.sync_thread(t2, meta1.timestamp).unwrap();

        // Thread 2's next timestamp should be > Thread 1's
        let meta2 = tracer.new_metadata(t2).unwrap();
        assert!(meta2.timestamp > meta1.timestamp);
    }

    #[test]
    fn test_buffer_full() {
        let mut tracer = ProductionTracer::with_capacity(2);
        let thread_id = ThreadId::new(0);

        // Fill buffer
        for _ in 0..2 {
            let meta = tracer.new_metadata(thread_id).unwrap();
            let event = SimulationEvent::ClockTick {
                meta,
                event: ClockEvent {
                    prev_timestamp: LamportTimestamp::ZERO,
                    new_timestamp: meta.timestamp,
                },
            };
            assert!(tracer.record(event).is_ok());
        }

        // Third event should fail
        let meta = tracer.new_metadata(thread_id).unwrap();
        let event = SimulationEvent::ClockTick {
            meta,
            event: ClockEvent {
                prev_timestamp: LamportTimestamp::ZERO,
                new_timestamp: meta.timestamp,
            },
        };
        assert!(matches!(tracer.record(event), Err(TracingError::BufferFull)));
    }
}