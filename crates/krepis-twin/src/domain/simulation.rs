//! Simulation Integration - The Zero-cost Razor Assembly
//!
//! # Design Philosophy
//!
//! This module brings together Clock and Memory through event-driven simulation
//! while maintaining the Zero-cost Razor principles:
//!
//! - **No Arc/Box**: Direct ownership of backends
//! - **Static Dispatch**: All polymorphism resolved at compile time
//! - **Stack-only (Kani)**: Verification mode uses zero heap allocation
//!
//! # Architecture
//!
//! ```text
//! Simulator<MB, CB>
//!   ├─ memory: SimulatedMemory<MB, CB>
//!   └─ Event processing via memory.clock_mut()
//!
//! EventDispatcher extracts and processes events
//! ```
//!
//! # TLA+ Correspondence
//!
//! The simulation implements the TLA+ Next state relation:
//! ```tla
//! Next ==
//!     \/ Tick          (process next event)
//!     \/ Write         (schedule write sync)
//!     \/ Fence         (schedule fence)
//!     \/ FlushOne      (commit buffer entry)
//! ```

use super::clock::{ClockBackend, EventPayload, ScheduledEvent};
use super::memory::{MemoryBackend, SimulatedMemory};

/// Event dispatcher for simulation
///
/// # Type Parameters
/// - `MB`: Memory backend (Production or Verification)
/// - `CB`: Clock backend (Production or Verification)
///
/// # Design Note
///
/// This struct doesn't own the memory or clock. Instead, it operates on
/// mutable references, allowing the Simulator to maintain ownership while
/// the dispatcher processes events.
///
/// # TLA+ Correspondence
///
/// The dispatcher implements event handlers for different event types,
/// each corresponding to a TLA+ action.
pub struct EventDispatcher;

impl EventDispatcher {
    /// Create new event dispatcher
    pub fn new() -> Self {
        Self
    }

    /// Process single event from clock
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// Tick ==
    ///     /\ eventQueue /= {}
    ///     /\ LET e == CHOOSE e \in eventQueue : (...)
    ///        IN ProcessEvent(e)
    /// ```
    ///
    /// # Algorithm
    /// 1. Pop next event from clock (via memory.clock_mut())
    /// 2. Dispatch to appropriate handler based on event type
    /// 3. Return whether an event was processed
    ///
    /// # Returns
    /// `true` if an event was processed, `false` if clock is idle
    pub fn process_event<MB: MemoryBackend, CB: ClockBackend>(
        &self,
        memory: &mut SimulatedMemory<MB, CB>,
    ) -> bool {
        // Get next event from clock
        let Some(event) = memory.clock_mut().tick() else {
            return false;
        };

        // Dispatch to handler
        self.dispatch_event(event, memory);
        true
    }

    /// Process all pending events until clock is idle
    ///
    /// # Kani Safety
    ///
    /// This method includes a safety limit to prevent unbounded loops
    /// in verification mode. Kani can't verify infinite loops, so we
    /// cap at a reasonable maximum (1000 events).
    ///
    /// # Returns
    /// Number of events processed
    pub fn process_all<MB: MemoryBackend, CB: ClockBackend>(
        &self,
        memory: &mut SimulatedMemory<MB, CB>,
    ) -> usize {
        let mut count = 0;
        const MAX_EVENTS: usize = 1000; // Safety limit for Kani

        while count < MAX_EVENTS && self.process_event(memory) {
            count += 1;
        }

        count
    }

    /// Dispatch event to appropriate handler
    ///
    /// # TLA+ Action Mapping
    ///
    /// Each event type maps to a TLA+ action:
    /// - `MemoryWriteSync` → `FlushOne(core)`
    /// - `MemoryFence` → `FlushAll(core)`
    /// - Others → Future extensions
    fn dispatch_event<MB: MemoryBackend, CB: ClockBackend>(
        &self,
        event: ScheduledEvent,
        memory: &mut SimulatedMemory<MB, CB>,
    ) {
        match event.payload {
            EventPayload::MemoryWriteSync { core, .. } => {
                let _ = memory.flush_one(core);
            }
            EventPayload::MemoryFence { core } => {
                while memory.get_buffer_len(core) > 0 {
                    let _ = memory.flush_one(core);
                }
            }
            // Razor Tip: 정의는 되어 있으나 시뮬레이션 핵심 로직이 아닌 것들은 
            // 한데 묶어서 처리합니다.
            EventPayload::Test(_) 
            | EventPayload::TaskReady { .. } 
            | EventPayload::WatchdogTimeout { .. } 
            | EventPayload::Custom(_) => {
                // 이 이벤트들은 로직상 무시하거나 로깅만 수행
            }
        }
    }
}

impl Default for EventDispatcher {
    fn default() -> Self {
        Self::new()
    }
}

/// Simulator - Top-level simulation controller
///
/// # Type Parameters
/// - `MB`: Memory backend (Production or Verification)
/// - `CB`: Clock backend (Production or Verification)
///
/// # Ownership Model
///
/// The Simulator **owns** the memory system, which in turn owns the clock.
/// This direct ownership eliminates Arc overhead and makes lifetime tracking
/// trivial for Kani.
///
/// ```text
/// Simulator<MB, CB>
///   └─ owns ─> SimulatedMemory<MB, CB>
///       └─ owns ─> VirtualClock<CB>
/// ```
///
/// # TLA+ Correspondence
///
/// ```tla
/// Simulation == INSTANCE VirtualClock WITH
///                 INSTANCE SimulatedMemory
/// ```
pub struct Simulator<MB: MemoryBackend, CB: ClockBackend> {
    /// Memory system (which owns the clock)
    memory: SimulatedMemory<MB, CB>,
    
    /// Event dispatcher (stateless)
    dispatcher: EventDispatcher,
}

impl<MB: MemoryBackend, CB: ClockBackend> Simulator<MB, CB> {
    /// Create new simulator
    ///
    /// # Arguments
    /// - `memory`: Configured memory system (already owns clock)
    ///
    /// # Example
    /// ```rust
    /// use krepis_twin::domain::simulation::Simulator;
    /// use krepis_twin::domain::memory::{SimulatedMemory, ProductionBackend as MemProd, MemoryConfig};
    /// use krepis_twin::domain::clock::{VirtualClock, ProductionBackend as ClockProd, TimeMode};
    ///
    /// let mem_backend = MemProd::new(4, 2);
    /// let clock = VirtualClock::new(ClockProd::new(), TimeMode::EventDriven);
    /// let memory = SimulatedMemory::new(mem_backend, clock, MemoryConfig::default());
    ///
    /// let mut simulator = Simulator::new(memory);
    /// ```
    pub fn new(memory: SimulatedMemory<MB, CB>) -> Self {
        Self {
            memory,
            dispatcher: EventDispatcher::new(),
        }
    }

    /// Get immutable reference to memory
    pub fn memory(&self) -> &SimulatedMemory<MB, CB> {
        &self.memory
    }

    /// Get mutable reference to memory
    pub fn memory_mut(&mut self) -> &mut SimulatedMemory<MB, CB> {
        &mut self.memory
    }

    /// Process single simulation step
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// Next ==
    ///     \/ Tick
    ///     \/ UNCHANGED vars
    /// ```
    ///
    /// # Returns
    /// `true` if a step was taken, `false` if simulation is idle
    pub fn step(&mut self) -> bool {
        self.dispatcher.process_event(&mut self.memory)
    }

    /// Run simulation until all events are processed
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// RunToCompletion ==
    ///     /\ eventQueue = {}
    ///     /\ \A core \in Cores : storeBuffers[core] = <<>>
    /// ```
    ///
    /// This is a convenience method that repeatedly calls `step()` until
    /// the clock is idle and all store buffers are flushed.
    ///
    /// # Returns
    /// Number of events processed
    pub fn run_until_idle(&mut self) -> usize {
        self.dispatcher.process_all(&mut self.memory)
    }

    /// Check if simulation is idle (no pending events)
    pub fn is_idle(&self) -> bool {
        self.memory.clock().is_idle()
    }

    /// Reset simulation to initial state
    ///
    /// # TLA+ Correspondence
    /// Returns to `Init` state
    pub fn reset(&mut self) {
        self.memory.reset();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::clock::{ProductionBackend as ProdClockBackend, TimeMode, VirtualClock};
    use crate::domain::memory::{MemoryConfig, ProductionBackend as ProdMemBackend};

    #[test]
    fn test_event_dispatcher_basic() {
        let mem_backend = ProdMemBackend::new(2, 2);
        let clock_backend = ProdClockBackend::new();
        let clock = VirtualClock::new(clock_backend, TimeMode::EventDriven);
        let config = MemoryConfig::default();
        let mut memory = SimulatedMemory::new(mem_backend, clock, config);

        let dispatcher = EventDispatcher::new();

        // Write creates an event
        memory.write(0, 0, 100).unwrap();
        assert!(!memory.clock_mut().is_idle());

        // Process the event
        assert!(dispatcher.process_event(&mut memory));
        assert_eq!(memory.read_main_memory(0), 100);
    }

    #[test]
    fn test_simulator_lifecycle() {
        let mem_backend = ProdMemBackend::new(2, 2);
        let clock_backend = ProdClockBackend::new();
        let clock = VirtualClock::new(clock_backend, TimeMode::EventDriven);
        let config = MemoryConfig::default();
        let memory = SimulatedMemory::new(mem_backend, clock, config);

        let mut sim = Simulator::new(memory);

        // Initial state
        assert!(sim.is_idle());

        // Write some data
        sim.memory_mut().write(0, 0, 100).unwrap();
        sim.memory_mut().write(0, 1, 200).unwrap();

        // Should have events now
        assert!(!sim.is_idle());

        // Run to completion
        let count = sim.run_until_idle();
        assert_eq!(count, 2);

        // Should be idle again
        assert!(sim.is_idle());

        // Data should be in main memory
        assert_eq!(sim.memory().read_main_memory(0), 100);
        assert_eq!(sim.memory().read_main_memory(1), 200);
    }

    #[test]
    fn test_simulator_fence() {
        let mem_backend = ProdMemBackend::new(2, 2);
        let clock_backend = ProdClockBackend::new();
        let clock = VirtualClock::new(clock_backend, TimeMode::EventDriven);
        let config = MemoryConfig::default();
        let memory = SimulatedMemory::new(mem_backend, clock, config);

        let mut sim = Simulator::new(memory);

        // Write and fence
        sim.memory_mut().write(0, 0, 100).unwrap();
        sim.memory_mut().write(0, 1, 200).unwrap();
        sim.memory_mut().fence(0).unwrap();

        // Run simulation
        sim.run_until_idle();

        // All writes should be visible
        assert_eq!(sim.memory().read_main_memory(0), 100);
        assert_eq!(sim.memory().read_main_memory(1), 200);
        assert!(sim.memory().all_buffers_empty());
    }

    #[test]
    fn test_simulator_reset() {
        let mem_backend = ProdMemBackend::new(2, 2);
        let clock_backend = ProdClockBackend::new();
        let clock = VirtualClock::new(clock_backend, TimeMode::EventDriven);
        let config = MemoryConfig::default();
        let memory = SimulatedMemory::new(mem_backend, clock, config);

        let mut sim = Simulator::new(memory);

        sim.memory_mut().write(0, 0, 100).unwrap();
        sim.run_until_idle();

        sim.reset();

        assert_eq!(sim.memory().read_main_memory(0), 0);
        assert!(sim.is_idle());
    }
}