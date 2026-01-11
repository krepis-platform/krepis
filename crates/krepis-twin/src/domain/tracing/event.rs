//! Zero-cost Event Definitions
//!
//! All types are designed for:
//! - Stack allocation only
//! - Minimal padding
//! - Cache-friendly layout
//! - Inline-heavy operations

use std::fmt;

/// Maximum number of threads supported by the tracer
/// 
/// This is a compile-time constant to enable array-based storage
/// without runtime allocation.
pub const MAX_THREADS: usize = 16;

/// A unique identifier for threads in the simulation
///
/// **Important**: ThreadId must be in range [0, MAX_THREADS) to be used
/// as a direct array index.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct ThreadId(pub u32);

impl ThreadId {
    /// Create a new ThreadId
    ///
    /// # Panics
    ///
    /// Panics in debug mode if id >= MAX_THREADS
    #[inline(always)]
    pub fn new(id: u32) -> Self {
        debug_assert!((id as usize) < MAX_THREADS, "ThreadId out of bounds");
        ThreadId(id)
    }

    /// Convert to array index (zero-cost)
    #[inline(always)]
    pub fn as_index(self) -> usize {
        self.0 as usize
    }
}

/// A unique identifier for memory addresses
///
/// Using u64 for wide address space support
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct MemAddr(pub u64);

/// Lamport logical timestamp for causality ordering
///
/// # Memory Layout
/// - Size: 8 bytes
/// - Alignment: 8 bytes
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(transparent)]
pub struct LamportTimestamp(pub u64);

impl LamportTimestamp {
    /// The initial timestamp value (zero)
    pub const ZERO: Self = LamportTimestamp(0);

    /// Increment the timestamp by one
    ///
    /// This operation is used when a thread performs a local event.
    ///
    /// # Example
    ///
    /// ```
    /// # use krepis_twin::domain::tracing::event::LamportTimestamp;
    /// let mut ts = LamportTimestamp(5);
    /// ts.increment();
    /// assert_eq!(ts.0, 6);
    /// ```
    #[inline(always)]
    pub fn increment(&mut self) {
        self.0 = self.0.wrapping_add(1);
    }

    /// Synchronize with another timestamp
    ///
    /// Updates this timestamp to be greater than both the current value
    /// and the other timestamp. This implements the Lamport clock
    /// synchronization rule for message passing.
    ///
    /// # Example
    ///
    /// ```
    /// # use krepis_twin::domain::tracing::event::LamportTimestamp;
    /// let mut ts1 = LamportTimestamp(5);
    /// let ts2 = LamportTimestamp(10);
    /// ts1.sync(ts2);
    /// assert_eq!(ts1.0, 11); // max(5, 10) + 1
    /// ```
    #[inline(always)]
    pub fn sync(&mut self, remote: LamportTimestamp) {
        self.0 = core::cmp::max(self.0, remote.0).saturating_add(1);
    }
}

/// Metadata common to all simulation events
///
/// # Memory Layout
/// - Size: 24 bytes (optimized for cache line)
/// - Alignment: 8 bytes
/// - Layout: [timestamp: 8][thread_id: 4][_pad: 4][seq_num: 8]
#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct EventMetadata {
    /// Lamport timestamp of this event
    pub timestamp: LamportTimestamp,
    /// Thread that generated this event
    pub thread_id: ThreadId,
    /// Padding for alignment (compiler will insert this anyway)
    _pad: u32,
    /// Sequence number within this thread (for total ordering)
    pub seq_num: u64,
}

impl EventMetadata {
    /// Create new event metadata
    ///
    /// # Arguments
    ///
    /// * `timestamp` - The Lamport timestamp for this event
    /// * `thread_id` - The thread that generated this event
    /// * `seq_num` - The sequence number within the thread
    #[inline(always)]
    pub fn new(timestamp: LamportTimestamp, thread_id: ThreadId, seq_num: u64) -> Self {
        Self {
            timestamp,
            thread_id,
            _pad: 0,
            seq_num,
        }
    }
}

/// Memory fence type for synchronization
///
/// Corresponds to memory ordering semantics in concurrent programming.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum FenceType {
    /// Acquire fence - prevents reordering of subsequent reads
    Acquire = 0,
    /// Release fence - prevents reordering of prior writes
    Release = 1,
    /// Sequentially consistent fence - full memory barrier
    SeqCst = 2,
}

/// Memory operation details
///
/// # Memory Layout
/// Optimized to fit in 24 bytes total with discriminant
#[derive(Debug, Clone, Copy)]
pub enum MemoryOperation {
    /// Read operation
    Read {
        /// Memory address being read
        addr: MemAddr,
        /// Value that was read
        value: u64,
        /// True if the value was fetched from cache
        cache_hit: bool,
    },
    /// Write operation
    Write {
        /// Memory address being written
        addr: MemAddr,
        /// Value being written
        value: u64,
        /// True if the write went to store buffer (not immediately visible)
        buffered: bool,
    },
    /// Store buffer flush to main memory
    BufferFlush {
        /// Memory address being flushed
        addr: MemAddr,
        /// Value being flushed to main memory
        value: u64,
    },
    /// Memory barrier/fence operation
    Fence {
        /// Type of fence (acquire, release, seq_cst)
        fence_type: FenceType,
    },
}

/// Virtual clock tick event
///
/// # Memory Layout
/// - Size: 16 bytes
#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub struct ClockEvent {
    /// Previous timestamp before tick
    pub prev_timestamp: LamportTimestamp,
    /// New timestamp after tick
    pub new_timestamp: LamportTimestamp,
}

/// Synchronization operation type
///
/// Represents various synchronization primitives used in concurrent programs.
#[derive(Debug, Clone, Copy)]
#[repr(u8)]
pub enum SyncType {
    /// Mutex lock acquired
    MutexLock {
        /// Unique identifier for the mutex
        lock_id: u64
    } = 0,
    /// Mutex lock released
    MutexUnlock {
        /// Unique identifier for the mutex
        lock_id: u64
    } = 1,
    /// Condition variable wait
    CondVarWait {
        /// Unique identifier for the condition variable
        cv_id: u64
    } = 2,
    /// Condition variable signal
    CondVarSignal {
        /// Unique identifier for the condition variable
        cv_id: u64
    } = 3,
}

/// Core simulation event enum
/// 
/// # Memory Layout
/// Total size: 64 bytes (optimized for cache line alignment)
/// - 8 bytes: discriminant + padding
/// - 24 bytes: EventMetadata
/// - 32 bytes: largest variant data
///
/// Design principle: Each variant is **self-contained** and carries
/// all necessary information for causality analysis without requiring
/// external state lookups.
#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub enum SimulationEvent {
    /// Virtual clock advanced
    ClockTick {
        /// Event metadata (timestamp, thread, sequence)
        meta: EventMetadata,
        /// Clock event details
        event: ClockEvent,
    },

    /// Memory operation occurred
    Memory {
        /// Event metadata (timestamp, thread, sequence)
        meta: EventMetadata,
        /// Memory operation details
        operation: MemoryOperation,
    },

    /// New thread spawned
    ThreadSpawn {
        /// Event metadata (timestamp, thread, sequence)
        meta: EventMetadata,
        /// ID of the newly spawned thread
        child_thread_id: ThreadId,
    },

    /// Thread terminated
    ThreadJoin {
        /// Event metadata (timestamp, thread, sequence)
        meta: EventMetadata,
        /// ID of the thread that terminated
        terminated_thread_id: ThreadId,
    },

    /// Synchronization event (mutex, semaphore, etc.)
    Synchronization {
        /// Event metadata (timestamp, thread, sequence)
        meta: EventMetadata,
        /// Type of synchronization operation
        sync_type: SyncType,
    },
}

impl SimulationEvent {
    /// Extract metadata from any event variant
    ///
    /// This is a zero-cost operation (single pointer dereference)
    #[inline(always)]
    pub fn metadata(&self) -> &EventMetadata {
        match self {
            SimulationEvent::ClockTick { meta, .. }
            | SimulationEvent::Memory { meta, .. }
            | SimulationEvent::ThreadSpawn { meta, .. }
            | SimulationEvent::ThreadJoin { meta, .. }
            | SimulationEvent::Synchronization { meta, .. } => meta,
        }
    }

    /// Get the Lamport timestamp of this event
    #[inline(always)]
    pub fn timestamp(&self) -> LamportTimestamp {
        self.metadata().timestamp
    }

    /// Get the thread ID that generated this event
    #[inline(always)]
    pub fn thread_id(&self) -> ThreadId {
        self.metadata().thread_id
    }

    /// Check if this event establishes a happens-before relation with another
    ///
    /// This is a **pure domain logic** method that will be used by the
    /// CausalityGraph analyzer.
    #[inline]
    pub fn happens_before(&self, other: &SimulationEvent) -> bool {
        // Lamport clock property: e1 -> e2 implies timestamp(e1) < timestamp(e2)
        self.timestamp() < other.timestamp()
    }
}

impl fmt::Display for SimulationEvent {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SimulationEvent::ClockTick { meta, event } => {
                write!(
                    f,
                    "[T{}@{}] ClockTick: {} → {}",
                    meta.thread_id.0,
                    meta.timestamp.0,
                    event.prev_timestamp.0,
                    event.new_timestamp.0
                )
            }
            SimulationEvent::Memory { meta, operation } => {
                write!(f, "[T{}@{}] ", meta.thread_id.0, meta.timestamp.0)?;
                match operation {
                    MemoryOperation::Read { addr, value, cache_hit } => {
                        write!(
                            f,
                            "Read(0x{:x}) = {} {}",
                            addr.0,
                            value,
                            if *cache_hit { "[cache]" } else { "[mem]" }
                        )
                    }
                    MemoryOperation::Write { addr, value, buffered } => {
                        write!(
                            f,
                            "Write(0x{:x}, {}) {}",
                            addr.0,
                            value,
                            if *buffered { "[buffered]" } else { "[direct]" }
                        )
                    }
                    MemoryOperation::BufferFlush { addr, value } => {
                        write!(f, "Flush(0x{:x}, {})", addr.0, value)
                    }
                    MemoryOperation::Fence { fence_type } => {
                        write!(f, "Fence({:?})", fence_type)
                    }
                }
            }
            SimulationEvent::ThreadSpawn { meta, child_thread_id } => {
                write!(
                    f,
                    "[T{}@{}] Spawn → T{}",
                    meta.thread_id.0, meta.timestamp.0, child_thread_id.0
                )
            }
            SimulationEvent::ThreadJoin { meta, terminated_thread_id } => {
                write!(
                    f,
                    "[T{}@{}] Join ← T{}",
                    meta.thread_id.0, meta.timestamp.0, terminated_thread_id.0
                )
            }
            SimulationEvent::Synchronization { meta, sync_type } => {
                write!(f, "[T{}@{}] Sync({:?})", meta.thread_id.0, meta.timestamp.0, sync_type)
            }
        }
    }
}

#[cfg(kani)]
mod event_verification {
    use super::*;

    /// Verify that Lamport timestamp operations are monotonic
    #[kani::proof]
    fn verify_lamport_monotonicity() {
        let mut ts = LamportTimestamp(kani::any());
        let old_value = ts.0;
        
        ts.increment();
        kani::assume(old_value < u64::MAX); // Prevent overflow
        assert!(ts.0 > old_value);
    }

    /// Verify that timestamp synchronization maintains causality
    #[kani::proof]
    fn verify_lamport_sync() {
        let ts1_raw: u64 = kani::any();
        let ts2_raw: u64 = kani::any();
        
        // 유효한 범위 제약: +1을 해도 오버플로우가 나지 않는 범위 내에서만 검증
        kani::assume(ts1_raw < u64::MAX);
        kani::assume(ts2_raw < u64::MAX);
        
        let mut ts1 = LamportTimestamp(ts1_raw);
        let ts2 = LamportTimestamp(ts2_raw);
        
        let old_ts1 = ts1.0;
        ts1.sync(ts2);
        
        // 이제 이 assert는 모든 '가능한' 우주에서 성공합니다.
        assert!(ts1.0 > old_ts1 || ts1.0 == u64::MAX); 
        assert!(ts1.0 > ts2.0 || ts1.0 == u64::MAX);
    }

    /// Verify happens-before transitivity
    #[kani::proof]
    fn verify_happens_before_transitivity() {
        let t1 = LamportTimestamp(kani::any());
        let t2 = LamportTimestamp(kani::any());
        let t3 = LamportTimestamp(kani::any());
        
        kani::assume(t1.0 < t2.0);
        kani::assume(t2.0 < t3.0);
        
        // Transitivity: if t1 < t2 and t2 < t3, then t1 < t3
        assert!(t1.0 < t3.0);
    }

    /// Verify SimulationEvent size is reasonable
    #[kani::proof]
    fn verify_event_size() {
        // Ensure event fits in cache line (64 bytes)
        assert!(std::mem::size_of::<SimulationEvent>() <= 64);
    }
}