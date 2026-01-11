//! Domain Layer - The Zero-cost Razor Assembly
//!
//! # Architecture Overview
//!
//! This module brings together all domain components with zero runtime overhead:
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────┐
//! │                    Domain Layer                             │
//! ├─────────────────────────────────────────────────────────────┤
//! │                                                             │
//! │  Clock Module                  Memory Module                │
//! │  ├─ VirtualClock<B>            ├─ SimulatedMemory<MB, CB>  │
//! │  ├─ ProductionBackend          ├─ ProductionBackend        │
//! │  └─ VerificationBackend        └─ VerificationBackend      │
//! │                                                             │
//! │                   Simulation Module                         │
//! │                   ├─ Simulator<MB, CB>                      │
//! │                   └─ EventDispatcher                        │
//! │                                                             │
//! │                    Tracing Module (Zero-cost)               │
//! │                    ├─ EventTracer<Backend>                  │
//! │                    ├─ ProductionTracer (heap)               │
//! │                    ├─ VerificationTracer (stack)            │
//! │                    ├─ SimulationEvent (64 bytes)            │
//! │                    └─ CausalityGraph (stack-only)           │
//! │                                                             │
//! └─────────────────────────────────────────────────────────────┘
//! ```
//!
//! # Type Aliases for Convenience
//!
//! We provide convenient aliases for common configurations:
//!
//! - `ProductionSimulator`: High-performance production mode
//! - `VerificationSimulator`: Kani-friendly verification mode
//! - `ProductionTracer`: Large-capacity heap-allocated tracer
//! - `VerificationTracer`: Small-capacity stack-allocated tracer
//!
//! # Monomorphization Magic
//!
//! When you use `ProductionSimulator`, the compiler generates:
//! ```text
//! Simulator
//!   ProductionBackend (Memory),
//!   ProductionBackend (Clock)
//! >
//!   └─ All method calls inlined
//!   └─ DashMap + RwLock optimized
//!   └─ Zero abstraction overhead
//! ```
//!
//! When you use `VerificationSimulator`, the compiler generates:
//! ```text
//! Simulator
//!   VerificationBackend (Memory),
//!   VerificationBackend (Clock)
//! >
//!   └─ All method calls inlined
//!   └─ Fixed arrays + RefCell
//!   └─ Kani can verify everything
//! ```
//!
//! # Zero-cost Observability with Tracing
//!
//! The tracing module provides **zero-allocation observability**:
//! - Records simulation events with Lamport timestamps
//! - Stack-allocated storage for verification (1000 events)
//! - Heap-allocated storage for production (configurable)
//! - Array-indexed thread states (no HashMap overhead)
//! - Inline-heavy hot paths for maximum performance
//! - Tracks causality relationships (happens-before)
//! - Enables deterministic replay and formal verification
//! - Generates marketplace-grade simulation reports
//!
//! ```rust
//! use krepis_twin::domain::*;
//! use krepis_twin::domain::tracing::{ProductionTracer, ThreadId};
//!
//! let mut tracer = ProductionTracer::with_capacity(10_000);
//! let thread_id = ThreadId::new(0);
//! let meta = tracer.new_metadata(thread_id).unwrap();
//! // Record events during simulation...
//! // Then analyze causality
//! let graph = tracing::CausalityGraph::from_trace(tracer.events());
//! ```

pub mod clock;
pub mod memory;
pub mod simulation;
pub mod tracing;

// Re-export commonly used types
pub use simulation::{EventDispatcher, Simulator};

// Re-export clock types
pub use clock::{
    EventId,
    EventPayload,
    LamportClock,
    ScheduledEvent,
    TimeMode,
    VirtualClock,
    VirtualTimeNs,
};

// Re-export memory types
pub use memory::{
    Address,
    Value,
    CoreId,
    StoreEntry,
    MemoryOp,
    ConsistencyModel,
    MemoryConfig,
    SimulatedMemory,
    StoreBuffer,
};

// Re-export tracing types (updated for zero-cost design)
pub use tracing::{
    // Core types
    EventTracer,
    TracerConfig,
    TracingError,
    SimulationEvent,
    EventMetadata,
    MemoryOperation,
    ClockEvent,
    FenceType,
    SyncType,
    CausalityGraph,
    HappensBeforeRelation,
    
    // Zero-cost backend types
    TracerBackend,
    ProductionBackend as ProductionTracerBackend,
    VerificationBackend as VerificationTracerBackend,
    
    // Convenient type aliases
    ProductionTracer,
    VerificationTracer,
    
    // Re-export from event module
    event::{ThreadId, MemAddr, LamportTimestamp, MAX_THREADS},
};

/// Production simulator with maximum performance
///
/// # Configuration
///
/// Uses:
/// - `ProductionBackend` for memory (DashMap + RwLock)
/// - `ProductionBackend` for clock (BinaryHeap + RwLock)
///
/// # Performance Characteristics
///
/// - Thread-safe: Multiple threads can access concurrently
/// - Lock-free reads: Main memory uses DashMap
/// - Dynamic capacity: Unlimited events and addresses
/// - O(log n) event scheduling
///
/// # Example
///
/// ```rust
/// use krepis_twin::domain::*;
/// use krepis_twin::domain::clock::{ProductionBackend as ProdClockBackend, TimeMode, VirtualClock};
/// use krepis_twin::domain::memory::{MemoryConfig, ProductionBackend as ProdMemBackend, SimulatedMemory};
///
/// // Create backends
/// let mem_backend = ProdMemBackend::new(16, 8);  // 16 cores, buffer size 8
/// let clock_backend = ProdClockBackend::new();
/// let clock = VirtualClock::new(clock_backend, TimeMode::EventDriven);
/// let memory = SimulatedMemory::new(mem_backend, clock, MemoryConfig::default());
///
/// // Create simulator
/// let mut sim = ProductionSimulator::new(memory);
///
/// // Use it
/// sim.memory_mut().write(0, 42, 100).unwrap();
/// sim.run_until_idle();
/// assert_eq!(sim.memory().read_main_memory(42), 100);
/// ```
pub type ProductionSimulator = Simulator<
    memory::ProductionBackend,
    clock::ProductionBackend,
>;

/// Verification simulator for Kani formal verification
///
/// # Configuration
///
/// Uses:
/// - `VerificationBackend` for memory (fixed arrays + RefCell)
/// - `VerificationBackend` for clock (fixed arrays + RefCell)
///
/// # Verification Characteristics
///
/// - Stack-only: No heap allocation
/// - Bounded capacity: 2 cores, 4 addresses, 2 buffer entries
/// - Single-threaded: No locks needed
/// - Kani-friendly: All operations verifiable
///
/// # Example
///
/// ```rust
/// use krepis_twin::domain::*;
/// use krepis_twin::domain::clock::{VerificationBackend as VerifClockBackend, TimeMode, VirtualClock};
/// use krepis_twin::domain::memory::{MemoryConfig, VerificationBackend as VerifMemBackend, SimulatedMemory};
///
/// // Create backends
/// let mem_backend = VerifMemBackend::new();
/// let clock_backend = VerifClockBackend::new();
/// let clock = VirtualClock::new(clock_backend, TimeMode::EventDriven);
/// let memory = SimulatedMemory::new(mem_backend, clock, MemoryConfig::default());
///
/// // Create simulator
/// let mut sim = VerificationSimulator::new(memory);
///
/// // Use it (same API as production!)
/// sim.memory_mut().write(0, 0, 100).unwrap();
/// sim.run_until_idle();
/// assert_eq!(sim.memory().read_main_memory(0), 100);
/// ```
pub type VerificationSimulator = Simulator<
    memory::VerificationBackend,
    clock::VerificationBackend,
>;

/// Factory for creating production simulators
///
/// This provides a convenient builder-style API for creating production
/// simulators with common configurations.
///
/// # Tracing Support
///
/// The builder can optionally enable tracing for observability:
///
/// ```rust
/// use krepis_twin::domain::*;
///
/// let mut builder = ProductionSimulatorBuilder::new()
///     .num_cores(8)
///     .buffer_size(4)
///     .enable_tracing(true)
///     .max_traced_events(100_000);
///
/// let (sim, tracer) = builder.build_with_tracer();
/// ```
pub struct ProductionSimulatorBuilder {
    num_cores: usize,
    buffer_size: usize,
    enable_tracing: bool,
    max_traced_events: usize,
    validate_causality: bool,
}

impl ProductionSimulatorBuilder {
    /// Create new builder with default configuration
    ///
    /// Defaults:
    /// - 4 cores
    /// - Buffer size 2
    /// - Tracing disabled
    /// - Max 100,000 traced events
    /// - Causality validation in debug mode only
    pub fn new() -> Self {
        Self {
            num_cores: 4,
            buffer_size: 2,
            enable_tracing: false,
            max_traced_events: tracing::DEFAULT_MAX_EVENTS,
            validate_causality: cfg!(debug_assertions),
        }
    }

    /// Set number of cores
    pub fn num_cores(mut self, num_cores: usize) -> Self {
        self.num_cores = num_cores;
        self
    }

    /// Set buffer size per core
    pub fn buffer_size(mut self, buffer_size: usize) -> Self {
        self.buffer_size = buffer_size;
        self
    }

    /// Enable or disable event tracing
    ///
    /// When enabled, the simulator will record all events for later analysis.
    /// This has minimal runtime overhead but increases memory usage.
    pub fn enable_tracing(mut self, enable: bool) -> Self {
        self.enable_tracing = enable;
        self
    }

    /// Set maximum number of events to trace
    ///
    /// This prevents unbounded memory growth. Once the limit is reached,
    /// no more events will be recorded.
    pub fn max_traced_events(mut self, max: usize) -> Self {
        self.max_traced_events = max;
        self
    }

    /// Enable runtime causality validation
    ///
    /// When enabled, the tracer validates that all events maintain
    /// happens-before relationships. This adds overhead but helps
    /// catch bugs early.
    ///
    /// Default: enabled in debug builds, disabled in release.
    pub fn validate_causality(mut self, validate: bool) -> Self {
        self.validate_causality = validate;
        self
    }

    /// Build the simulator
    ///
    /// Returns a production simulator configured according to the builder settings.
    ///
    /// # Note
    ///
    /// The returned simulator does not have a tracer attached.
    /// Use `build_with_tracer()` if you need tracing support.
    pub fn build(self) -> ProductionSimulator {
        let mem_backend = memory::ProductionBackend::new(self.num_cores, self.buffer_size);
        let clock_backend = clock::ProductionBackend::new();
        let clock = clock::VirtualClock::new(clock_backend, clock::TimeMode::EventDriven);
        
        let config = memory::MemoryConfig {
            num_cores: self.num_cores,
            max_buffer_size: self.buffer_size,
            consistency_model: memory::ConsistencyModel::Relaxed,
            initial_size: 1024, // Reasonable default for production
        };
        
        let memory = memory::SimulatedMemory::new(mem_backend, clock, config);
        ProductionSimulator::new(memory)
    }

    /// Build the simulator with an attached tracer
    ///
    /// This is a convenience method that creates both the simulator and
    /// a configured tracer in one step.
    ///
    /// # Returns
    ///
    /// A tuple of (simulator, tracer) where the tracer is configured
    /// according to the builder's tracing settings.
    ///
    /// # Example
    ///
    /// ```rust
    /// use krepis_twin::domain::*;
    ///
    /// let (mut sim, mut tracer) = ProductionSimulatorBuilder::new()
    ///     .enable_tracing(true)
    ///     .max_traced_events(50_000)
    ///     .build_with_tracer();
    ///
    /// // Use tracer to record events...
    /// let thread_id = ThreadId::new(0);
    /// let meta = tracer.new_metadata(thread_id).unwrap();
    /// ```
    pub fn build_with_tracer(self) -> (ProductionSimulator, ProductionTracer) {
        let max_events = if self.enable_tracing {
            self.max_traced_events
        } else {
            0 // No events if tracing disabled
        };

        let backend = ProductionTracerBackend::new(max_events);
        let config = TracerConfig {
            max_events,
            validate_causality: self.validate_causality,
        };

        let tracer = EventTracer::new(backend, config);
        let simulator = self.build();
        
        (simulator, tracer)
    }
}

impl Default for ProductionSimulatorBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// Factory for creating verification simulators
///
/// This ensures proper configuration for Kani verification mode.
/// Tracing is always enabled in verification mode to aid debugging.
pub struct VerificationSimulatorBuilder;

impl VerificationSimulatorBuilder {
    /// Create verification simulator
    ///
    /// Uses fixed configuration suitable for Kani:
    /// - 2 cores
    /// - 2 buffer entries per core
    /// - 4 addresses
    pub fn build() -> VerificationSimulator {
        let mem_backend = memory::VerificationBackend::new();
        let clock_backend = clock::VerificationBackend::new();
        let clock = clock::VirtualClock::new(clock_backend, clock::TimeMode::EventDriven);
        
        let config = memory::MemoryConfig {
            num_cores: 2,
            max_buffer_size: 2,
            consistency_model: memory::ConsistencyModel::Relaxed,
            initial_size: 4,
        };
        
        let memory = memory::SimulatedMemory::new(mem_backend, clock, config);
        VerificationSimulator::new(memory)
    }

    /// Build with attached tracer for verification
    ///
    /// Returns a simulator and tracer configured for Kani verification.
    /// The tracer has strict limits to keep state space bounded.
    ///
    /// # Configuration
    /// - Max 1000 events (stack-allocated)
    /// - Causality validation always enabled
    /// - Zero heap allocation
    pub fn build_with_tracer() -> (VerificationSimulator, VerificationTracer) {
        let backend = VerificationTracerBackend::new();
        let config = TracerConfig {
            max_events: VerificationTracerBackend::MAX_EVENTS,
            validate_causality: true, // Always validate in verification
        };

        let tracer = EventTracer::new(backend, config);
        let simulator = Self::build();
        
        (simulator, tracer)
    }
}

/// Helper trait for integrating tracing with simulators
///
/// This trait provides ergonomic methods for recording simulation events.
/// It will be implemented in the infrastructure layer where we have access
/// to mutable tracer state.
///
/// # Example Usage (Future)
///
/// ```ignore
/// // This will work once infrastructure layer is implemented
/// let mut sim = ProductionSimulator::new(...);
/// let mut tracer = ProductionTracer::with_capacity(10_000);
///
/// // Record memory operation
/// sim.trace_memory_read(&mut tracer, thread_id, addr, value);
///
/// // Record clock tick
/// sim.trace_clock_tick(&mut tracer, thread_id, old_ts, new_ts);
/// ```
pub trait TracingAdapter {
    /// Record a memory read operation
    fn trace_memory_read(
        &self,
        tracer: &mut ProductionTracer,
        thread_id: ThreadId,
        addr: Address,
        value: Value,
        cache_hit: bool,
    );

    /// Record a memory write operation
    fn trace_memory_write(
        &self,
        tracer: &mut ProductionTracer,
        thread_id: ThreadId,
        addr: Address,
        value: Value,
        buffered: bool,
    );

    /// Record a store buffer flush
    fn trace_buffer_flush(
        &self,
        tracer: &mut ProductionTracer,
        thread_id: ThreadId,
        addr: Address,
        value: Value,
    );

    /// Record a clock tick
    fn trace_clock_tick(
        &self,
        tracer: &mut ProductionTracer,
        thread_id: ThreadId,
        prev_timestamp: LamportTimestamp,
        new_timestamp: LamportTimestamp,
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_production_simulator_builder() {
        let mut sim = ProductionSimulatorBuilder::new()
            .num_cores(8)
            .buffer_size(4)
            .build();

        sim.memory_mut().write(0, 100, 42).unwrap();
        sim.run_until_idle();
        assert_eq!(sim.memory().read_main_memory(100), 42);
    }

    #[test]
    fn test_production_simulator_with_tracer() {
        let (mut sim, _tracer) = ProductionSimulatorBuilder::new()
            .num_cores(4)
            .buffer_size(2)
            .enable_tracing(true)
            .max_traced_events(1000)
            .build_with_tracer();

        sim.memory_mut().write(0, 100, 42).unwrap();
        sim.run_until_idle();
        assert_eq!(sim.memory().read_main_memory(100), 42);

        // Tracer is returned but not yet integrated
        // Integration will happen in infrastructure layer
    }

    #[test]
    fn test_verification_simulator_builder() {
        let mut sim = VerificationSimulatorBuilder::build();

        sim.memory_mut().write(0, 0, 42).unwrap();
        sim.run_until_idle();
        assert_eq!(sim.memory().read_main_memory(0), 42);
    }

    #[test]
    fn test_verification_simulator_with_tracer() {
        let (mut sim, mut _tracer) = VerificationSimulatorBuilder::build_with_tracer();

        sim.memory_mut().write(0, 0, 42).unwrap();
        sim.run_until_idle();
        assert_eq!(sim.memory().read_main_memory(0), 42);

        // Verify tracer configuration
        assert_eq!(_tracer.event_count(), 0); // No events recorded yet
        assert_eq!(_tracer.global_timestamp(), LamportTimestamp::ZERO);
    }

    #[test]
    fn test_tracer_standalone() {
        let mut tracer = ProductionTracer::with_capacity(100);
        
        let thread_id = ThreadId::new(0);
        let meta = tracer.new_metadata(thread_id).unwrap();
        assert_eq!(meta.timestamp.0, 1);
        
        let event = SimulationEvent::ClockTick {
            meta,
            event: ClockEvent {
                prev_timestamp: LamportTimestamp::ZERO,
                new_timestamp: meta.timestamp,
            },
        };

        assert!(tracer.record(event).is_ok());
        assert_eq!(tracer.event_count(), 1);
        
        // Verify causality
        assert!(tracer.verify_causality().is_ok());
    }

    #[test]
    fn test_verification_tracer_standalone() {
        let mut tracer = VerificationTracer::new_verification();
        
        let thread_id = ThreadId::new(0);
        let meta = tracer.new_metadata(thread_id).unwrap();
        assert_eq!(meta.timestamp.0, 1);
        
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
    fn test_type_aliases_work() {
        // Just verify the types compile
        let mem_backend = memory::ProductionBackend::new(2, 2);
        let clock_backend = clock::ProductionBackend::new();
        let clock = clock::VirtualClock::new(clock_backend, clock::TimeMode::EventDriven);
        let memory = memory::SimulatedMemory::new(mem_backend, clock, memory::MemoryConfig::default());
        let _sim: ProductionSimulator = Simulator::new(memory);

        let mem_backend = memory::VerificationBackend::new();
        let clock_backend = clock::VerificationBackend::new();
        let clock = clock::VirtualClock::new(clock_backend, clock::TimeMode::EventDriven);
        let memory = memory::SimulatedMemory::new(mem_backend, clock, memory::MemoryConfig::default());
        let _sim: VerificationSimulator = Simulator::new(memory);
    }

    #[test]
    fn test_builder_tracing_configuration() {
        let builder = ProductionSimulatorBuilder::new()
            .enable_tracing(true)
            .max_traced_events(50000)
            .validate_causality(true);

        // Verify configuration is stored (will be used in build_with_tracer)
        assert!(builder.enable_tracing);
        assert_eq!(builder.max_traced_events, 50000);
        assert!(builder.validate_causality);
    }

    #[test]
    fn test_causality_graph_integration() {
        let mut tracer = ProductionTracer::with_capacity(100);
        
        // Record sequence of events
        let events = vec![
            (ThreadId::new(0), "Event 1"),
            (ThreadId::new(0), "Event 2"),
            (ThreadId::new(1), "Event 3"),
        ];

        for (tid, _desc) in events {
            let meta = tracer.new_metadata(tid).unwrap();
            let event = SimulationEvent::ClockTick {
                meta,
                event: ClockEvent {
                    prev_timestamp: LamportTimestamp(0),
                    new_timestamp: meta.timestamp,
                },
            };
            tracer.record(event).unwrap();
        }

        // Analyze causality
        let graph = CausalityGraph::from_trace(tracer.events());
        assert_eq!(graph.event_count(), 3);
        
        // Events 0 and 1 are from same thread, so happens-before holds
        assert!(graph.happens_before(0, 1));
        assert!(!graph.happens_before(1, 0));
    }

    #[test]
    fn test_thread_id_bounds_checking() {
        let mut tracer = ProductionTracer::with_capacity(100);
        
        // Valid thread ID (within MAX_THREADS)
        let valid_id = ThreadId::new(0);
        assert!(tracer.new_metadata(valid_id).is_ok());
        
        // In debug mode, ThreadId::new() will panic for out-of-bounds
        // In release mode, it's UB but we have runtime checks in new_metadata
        
        #[cfg(not(debug_assertions))]
        {
            // This would be UB in release, so we test the validation in new_metadata
            let invalid_id = ThreadId(MAX_THREADS as u32);
            assert!(matches!(
                tracer.new_metadata(invalid_id),
                Err(TracingError::InvalidThreadId(_))
            ));
        }
    }

    #[test]
    fn test_zero_allocation_verification_tracer() {
        // This test verifies that VerificationTracer doesn't allocate
        // We can't directly test for zero allocation, but we can verify
        // it works with the stack-allocated backend
        let mut tracer = VerificationTracer::new_verification();
        
        // Fill up to capacity
        for i in 0..10 {
            let tid = ThreadId::new((i % 2) as u32);
            let meta = tracer.new_metadata(tid).unwrap();
            let event = SimulationEvent::ClockTick {
                meta,
                event: ClockEvent {
                    prev_timestamp: LamportTimestamp(i),
                    new_timestamp: meta.timestamp,
                },
            };
            assert!(tracer.record(event).is_ok());
        }
        
        assert_eq!(tracer.event_count(), 10);
        assert!(tracer.verify_causality().is_ok());
    }

    #[test]
    fn test_causality_graph_zero_allocation() {
        // CausalityGraph should only allocate for topological_order()
        let mut tracer = ProductionTracer::with_capacity(10);
        
        for i in 0..5 {
            let tid = ThreadId::new(0);
            let meta = tracer.new_metadata(tid).unwrap();
            let event = SimulationEvent::ClockTick {
                meta,
                event: ClockEvent {
                    prev_timestamp: LamportTimestamp(i),
                    new_timestamp: meta.timestamp,
                },
            };
            tracer.record(event).unwrap();
        }
        
        // Creating graph is zero-allocation
        let graph = CausalityGraph::from_trace(tracer.events());
        assert_eq!(graph.event_count(), 5);
        
        // happens_before is zero-allocation
        assert!(graph.happens_before(0, 4));
        
        // topological_order allocates a Vec (only allocation in the module)
        let order = graph.topological_order();
        assert_eq!(order.len(), 5);
    }
}