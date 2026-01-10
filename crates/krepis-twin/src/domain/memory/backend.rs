//! Memory Backend Abstraction Layer - The Zero-cost Razor
//!
//! # Design Philosophy
//!
//! This trait provides a **compile-time polymorphic interface** for memory
//! operations, enabling us to swap between production (heap-allocated, concurrent)
//! and verification (stack-allocated, sequential) implementations with zero overhead.
//!
//! # TLA+ Correspondence
//! ```tla
//! VARIABLES mainMemory, storeBuffers
//! ```
//!
//! The backend trait maps to these TLA+ state variables while remaining
//! implementation-agnostic.

use super::types::{Address, CoreId, StoreEntry, Value};

/// Backend abstraction for memory state management
///
/// # Static Dispatch Magic
///
/// When you write `SimulatedMemory<ProductionBackend>`, the compiler generates
/// specialized code where every `backend.read_main()` call is inlined to the
/// actual DashMap lookup. No vtable, no indirection, pure speed.
///
/// # TLA+ State Variables
/// - Main memory: `mainMemory[addr] -> value`
/// - Store buffers: `storeBuffers[core] -> Seq(StoreEntry)`
pub trait MemoryBackend {
    /// Read from main memory (bypassing store buffers)
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// mainMemory[addr]
    /// ```
    fn read_main(&self, addr: Address) -> Value;

    /// Write to main memory (direct commit, no buffering)
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// mainMemory' = [mainMemory EXCEPT ![addr] = val]
    /// ```
    fn write_main(&mut self, addr: Address, val: Value);

    /// Check if store buffer for core is empty
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// storeBuffers[core] = <<>>
    /// ```
    fn is_buffer_empty(&self, core: CoreId) -> bool;

    /// Get current buffer size for core
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// Len(storeBuffers[core])
    /// ```
    fn buffer_len(&self, core: CoreId) -> usize;

    /// Push entry to store buffer
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// storeBuffers' = [storeBuffers EXCEPT 
    ///     ![core] = Append(@, [addr |-> addr, val |-> val])]
    /// ```
    ///
    /// # Returns
    /// `Ok(())` if successful, `Err` if buffer is full
    fn buffer_push(&mut self, core: CoreId, entry: StoreEntry) -> Result<(), &'static str>;

    /// Pop oldest entry from store buffer (FIFO head)
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// LET entry == Head(storeBuffers[core])
    /// IN storeBuffers' = [storeBuffers EXCEPT ![core] = Tail(@)]
    /// ```
    fn buffer_pop(&mut self, core: CoreId) -> Option<StoreEntry>;

    /// Lookup most recent value for address in buffer (local forwarding)
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// BufferLookup(core, addr) ==
    ///     LET buf == storeBuffers[core]
    ///         matching == {i \in 1..Len(buf) : buf[i].addr = addr}
    ///     IN  IF matching = {} THEN "NONE"
    ///         ELSE buf[CHOOSE x \in matching : \A y \in matching : x >= y].val
    /// ```
    fn buffer_lookup(&self, core: CoreId, addr: Address) -> Option<Value>;

    /// Clear all buffers (for reset)
    fn clear_all(&mut self);

    /// Get total number of cores supported
    fn num_cores(&self) -> usize;

    /// Get maximum buffer size per core
    fn max_buffer_size(&self) -> usize;
}

/// Helper trait for backends that need configuration
pub trait ConfigurableBackend: MemoryBackend + Sized {
    /// Create backend with specific configuration
    fn with_config(num_cores: usize, max_buffer_size: usize) -> Self;
}