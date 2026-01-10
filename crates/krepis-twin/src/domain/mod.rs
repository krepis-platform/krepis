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
//! └─────────────────────────────────────────────────────────────┘
//! ```
//!
//! # Type Aliases for Convenience
//!
//! We provide convenient aliases for common configurations:
//!
//! - `ProductionSimulator`: High-performance production mode
//! - `VerificationSimulator`: Kani-friendly verification mode
//!
//! # Monomorphization Magic
//!
//! When you use `ProductionSimulator`, the compiler generates:
//! ```text
//! Simulator<
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
//! Simulator<
//!   VerificationBackend (Memory),
//!   VerificationBackend (Clock)
//! >
//!   └─ All method calls inlined
//!   └─ Fixed arrays + RefCell
//!   └─ Kani can verify everything
//! ```

pub mod clock;
pub mod memory;
pub mod simulation;

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
pub struct ProductionSimulatorBuilder {
    num_cores: usize,
    buffer_size: usize,
}

impl ProductionSimulatorBuilder {
    /// Create new builder with default configuration
    ///
    /// Defaults:
    /// - 4 cores
    /// - Buffer size 2
    pub fn new() -> Self {
        Self {
            num_cores: 4,
            buffer_size: 2,
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

    /// Build the simulator
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
}

impl Default for ProductionSimulatorBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// Factory for creating verification simulators
///
/// This ensures proper configuration for Kani verification mode.
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
    fn test_verification_simulator_builder() {
        let mut sim = VerificationSimulatorBuilder::build();

        sim.memory_mut().write(0, 0, 42).unwrap();
        sim.run_until_idle();
        assert_eq!(sim.memory().read_main_memory(0), 42);
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
}