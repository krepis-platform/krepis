//! Simulated Memory Module
//!
//! # TLA+ Correspondence
//! Implements SimulatedMemory.tla specification
//!
//! # Physical Laws Enforced
//! - **M-001**: Sequential Consistency (when enabled)
//! - **M-002**: Atomic Integrity - No torn reads/writes
//! - **M-003**: Store Buffer Semantics - Relaxed memory model

//! Simulated Memory Module - The Zero-cost Razor
//!
//! # Architecture
//!
//! ```text
//! SimulatedMemory<MB: MemoryBackend, CB: ClockBackend>
//!     ├─ memory_backend: MB      (Production or Verification)
//!     ├─ clock: VirtualClock<CB> (Event scheduling)
//!     └─ config: MemoryConfig
//! ```
//!
//! # Monomorphization Magic
//!
//! When you write:
//! ```rust
//! use krepis_twin::domain::memory::{SimulatedMemory, ProductionBackend, MemoryConfig};
//! use krepis_twin::domain::clock::{VirtualClock, ProductionBackend as ClockProd, TimeMode};
//!
//! let mem_backend = ProductionBackend::new(2, 4);
//! let clock = VirtualClock::new(ClockProd::new(), TimeMode::EventDriven);
//! let config = MemoryConfig::default();
//!
//! let memory = SimulatedMemory::new(mem_backend, clock, config);
//! ```
//!
//! The compiler generates specialized code where:
//! - `memory_backend.read_main()` → inlines to DashMap::get()
//! - `clock.schedule()` → inlines to BinaryHeap::push()
//!
//! No vtables, no indirection, pure static dispatch!

mod types;
mod ops;
mod backend;
mod production_backend;
mod verification_backend;

#[cfg(kani)]
mod proofs;

pub use types::{
    Address, Value, CoreId, StoreEntry, MemoryOp,
    ConsistencyModel, MemoryConfig,
};
pub use ops::StoreBuffer;
pub use backend::{MemoryBackend, ConfigurableBackend};
pub use production_backend::ProductionBackend;
pub use verification_backend::VerificationBackend;

use crate::domain::clock::{ClockBackend, EventPayload, VirtualClock};

/// Simulated memory system with pluggable backends
///
/// # Type Parameters
/// - `MB`: Memory backend (Production or Verification)
/// - `CB`: Clock backend (for event scheduling)
///
/// # TLA+ Correspondence
/// ```tla
/// VARIABLES mainMemory, storeBuffers
/// ```
pub struct SimulatedMemory<MB: MemoryBackend, CB: ClockBackend> {
    /// Memory backend (direct ownership, no Arc!)
    backend: MB,
    
    /// Virtual clock for event scheduling (direct ownership!)
    clock: VirtualClock<CB>,
    
    /// Configuration
    config: MemoryConfig,
}

impl<MB: MemoryBackend, CB: ClockBackend> SimulatedMemory<MB, CB> {
    /// Create new simulated memory
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// Init ==
    ///     /\ mainMemory = [a \in Addresses |-> 0]
    ///     /\ storeBuffers = [c \in Cores |-> <<>>]
    /// ```
    pub fn new(backend: MB, clock: VirtualClock<CB>, config: MemoryConfig) -> Self {
        Self {
            backend,
            clock,
            config,
        }
    }

    /// Read value from address
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// ReadValue(core, addr) ==
    ///     LET bufVal == BufferLookup(core, addr)
    ///     IN  IF bufVal /= "NONE" THEN bufVal ELSE mainMemory[addr]
    /// ```
    ///
    /// # Algorithm
    /// 1. Check store buffer first (local forwarding)
    /// 2. If found, return buffered value
    /// 3. Otherwise, read from main memory
    pub fn read(&self, core: CoreId, addr: Address) -> Value {
        // Local forwarding: check this core's buffer first
        if let Some(val) = self.backend.buffer_lookup(core, addr) {
            return val;
        }
        
        // Fallback to main memory
        self.backend.read_main(addr)
    }

    /// Write value to address (buffered)
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// Write(core, addr, val) ==
    ///     /\ Len(storeBuffers[core]) < MaxBufferSize
    ///     /\ LET newLamport == lamportClock + 1
    ///        IN  /\ storeBuffers' = [storeBuffers EXCEPT 
    ///                ![core] = Append(@, [addr |-> addr, val |-> val])]
    ///            /\ eventQueue' = eventQueue \cup {CreateEvent("WRITE_SYNC", ...)}
    ///            /\ lamportClock' = newLamport
    /// ```
    pub fn write(&mut self, core: CoreId, addr: Address, val: Value) -> Result<(), &'static str> {
        // Add to store buffer
        let entry = StoreEntry::new(addr, val);
        self.backend.buffer_push(core, entry)?;
        
        // Schedule sync event (flush to main memory on next tick)
        let delay_ns = 1;
        self.clock.schedule(delay_ns, EventPayload::MemoryWriteSync { core, addr, value: val });
        
        Ok(())
    }

    /// Flush one entry from store buffer to main memory
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// FlushOneEntry(core) ==
    ///     LET entry == Head(storeBuffers[core])
    ///     IN  /\ mainMemory' = [mainMemory EXCEPT ![entry.addr] = entry.val]
    ///         /\ storeBuffers' = [storeBuffers EXCEPT ![core] = Tail(@)]
    /// ```
    pub fn flush_one(&mut self, core: CoreId) -> Result<(), &'static str> {
        let entry = self.backend.buffer_pop(core)
            .ok_or("Store buffer empty")?;
        
        // Write to main memory
        self.backend.write_main(entry.addr, entry.val);
        
        Ok(())
    }

    /// Memory fence - flush all pending writes
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// Fence(core) ==
    ///     /\ storeBuffers[core] /= <<>>
    ///     /\ eventQueue' = eventQueue \cup {CreateEvent("FENCE", ...)}
    /// ```
    pub fn fence(&mut self, core: CoreId) -> Result<(), &'static str> {
        if self.backend.is_buffer_empty(core) {
            return Ok(());
        }
        
        // Schedule fence event
        self.clock.schedule(1, EventPayload::MemoryFence { core });
        
        Ok(())
    }

    /// Get current value from main memory (bypass buffers)
    pub fn read_main_memory(&self, addr: Address) -> Value {
        self.backend.read_main(addr)
    }

    /// Get store buffer state for inspection
    pub fn get_buffer_len(&self, core: CoreId) -> usize {
        self.backend.buffer_len(core)
    }

    /// Check if all store buffers are empty
    pub fn all_buffers_empty(&self) -> bool {
        (0..self.backend.num_cores())
            .all(|core| self.backend.is_buffer_empty(core))
    }

    /// Get configuration
    pub fn config(&self) -> &MemoryConfig {
        &self.config
    }

    /// Non Mutable Clock
    pub fn clock(&self) -> &VirtualClock<CB> {
        &self.clock
    }

    /// Get mutable access to clock (for event processing)
    pub fn clock_mut(&mut self) -> &mut VirtualClock<CB> {
        &mut self.clock
    }

    /// Reset to initial state
    pub fn reset(&mut self) {
        self.backend.clear_all();
        self.clock.reset();
    }
}

// Type aliases for convenience
use crate::domain::clock::{ProductionBackend as ProdClockBackend, VerificationBackend as VerifClockBackend};

/// Production memory (full performance)
pub type ProductionMemory = SimulatedMemory<ProductionBackend, ProdClockBackend>;

/// Verification memory (Kani-friendly)
pub type VerificationMemory = SimulatedMemory<VerificationBackend, VerifClockBackend>;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::clock::TimeMode;

    #[test]
    fn test_production_memory() {
        let mem_backend = ProductionBackend::new(2, 2);
        let clock_backend = ProdClockBackend::new();
        let clock = VirtualClock::new(clock_backend, TimeMode::EventDriven);
        let config = MemoryConfig::default();
        
        let mut mem = SimulatedMemory::new(mem_backend, clock, config);
        
        mem.write(0, 0, 100).unwrap();
        assert_eq!(mem.read(0, 0), 100);
        assert_eq!(mem.read_main_memory(0), 0); // Not flushed yet
    }

    #[test]
    fn test_verification_memory() {
        let mem_backend = VerificationBackend::new();
        let clock_backend = VerifClockBackend::new();
        let clock = VirtualClock::new(clock_backend, TimeMode::EventDriven);
        let config = MemoryConfig::default();
        
        let mut mem = SimulatedMemory::new(mem_backend, clock, config);
        
        mem.write(0, 0, 100).unwrap();
        assert_eq!(mem.read(0, 0), 100);
    }

    #[test]
    fn test_flush() {
        let mem_backend = ProductionBackend::new(2, 2);
        let clock_backend = ProdClockBackend::new();
        let clock = VirtualClock::new(clock_backend, TimeMode::EventDriven);
        let config = MemoryConfig::default();
        
        let mut mem = SimulatedMemory::new(mem_backend, clock, config);
        
        mem.write(0, 0, 100).unwrap();
        mem.flush_one(0).unwrap();
        
        assert_eq!(mem.read_main_memory(0), 100);
        assert!(mem.all_buffers_empty());
    }
}