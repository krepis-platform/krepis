//! Verification Memory Backend - Kani's Best Friend
//!
//! # The Kani Whisperer Strategy
//!
//! Every design decision here is made with one goal: make Kani's symbolic
//! execution engine able to explore the entire state space without exploding.
//!
//! ## What We Eliminated
//! - ❌ Heap allocation → State space becomes infinite
//! - ❌ OS syscalls (RwLock) → Kani can't model OS
//! - ❌ Complex data structures → Too many invariants to track
//!
//! ## What We Use Instead
//! - ✅ Fixed-size arrays → Bounded state space (4 addresses, 2 cores, 2 buffers)
//! - ✅ UnsafeCell → Interior mutability without locks
//! - ✅ RefCell → Runtime borrow checking (Kani can model this!)
//! - ✅ Simple indexing → Kani loves direct memory access
//!
//! # Memory Layout (The Sashimi Slice)
//!
//! ```text
//! VerificationBackend (on stack, ~200 bytes total)
//! ├─ main_memory: UnsafeCell<[Value; 4]>       (32 bytes)
//! │   ├─ [0]: 0                                (8 bytes each)
//! │   ├─ [1]: 0
//! │   ├─ [2]: 0
//! │   └─ [3]: 0
//! ├─ store_buffers: [RefCell<BufferState>; 2] (144 bytes)
//! │   ├─ [0]: RefCell {
//! │   │   entries: [Option<StoreEntry>; 2],    (48 bytes)
//! │   │   count: usize                         (8 bytes)
//! │   │ }
//! │   └─ [1]: RefCell { ... }
//! ├─ num_cores: 2                              (8 bytes)
//! └─ max_buffer_size: 2                        (8 bytes)
//! ```
//!
//! Total state space for Kani to explore:
//! - 4 addresses × 2^64 possible values = manageable (Kani uses symbolic values)
//! - 2 cores × 2 buffer slots × 2 states (Some/None) = 2^4 = 16 combinations
//! - This is TINY compared to heap-allocated structures!

use super::backend::{ConfigurableBackend, MemoryBackend};
use super::types::{Address, CoreId, StoreEntry, Value};
use std::cell::{RefCell, UnsafeCell};

/// Maximum addresses for verification (must be small for Kani)
const MAX_ADDRESSES: usize = 4;

/// Maximum cores for verification
const MAX_CORES: usize = 2;

/// Maximum buffer entries per core
const MAX_BUFFER_ENTRIES: usize = 2;

/// Store buffer state (per core)
#[derive(Clone)]
struct BufferState {
    /// Fixed-size array of buffer entries
    /// Option<StoreEntry> allows us to represent "empty slots"
    entries: [Option<StoreEntry>; MAX_BUFFER_ENTRIES],
    
    /// Number of valid entries (optimization to avoid scanning)
    count: usize,
}

impl BufferState {
    fn new() -> Self {
        Self {
            entries: [None; MAX_BUFFER_ENTRIES],
            count: 0,
        }
    }

    /// Push entry to buffer (finds first empty slot)
    fn push(&mut self, entry: StoreEntry) -> Result<(), &'static str> {
        if self.count >= MAX_BUFFER_ENTRIES {
            return Err("Buffer full");
        }

        // Find first None slot (linear scan is fine for small arrays)
        for slot in &mut self.entries {
            if slot.is_none() {
                *slot = Some(entry);
                self.count += 1;
                return Ok(());
            }
        }

        Err("Buffer full")
    }

    /// Pop oldest entry (FIFO: find first Some, shift rest)
    ///
    /// # Algorithm
    /// 1. Find first Some entry
    /// 2. Extract it
    /// 3. Shift all subsequent entries left
    /// 4. Set last slot to None
    fn pop(&mut self) -> Option<StoreEntry> {
        if self.count == 0 {
            return None;
        }

        // Find first Some entry
        let first_idx = self.entries.iter().position(|e| e.is_some())?;
        let entry = self.entries[first_idx].take();

        // Shift remaining entries left
        for i in first_idx..MAX_BUFFER_ENTRIES - 1 {
            self.entries[i] = self.entries[i + 1].take();
        }
        self.entries[MAX_BUFFER_ENTRIES - 1] = None;

        self.count -= 1;
        entry
    }

    /// Lookup most recent value for address (scan backwards)
    fn lookup(&self, addr: Address) -> Option<Value> {
        // Scan from end to beginning (most recent first)
        for entry in self.entries.iter().rev() {
            if let Some(e) = entry {
                if e.addr == addr {
                    return Some(e.val);
                }
            }
        }
        None
    }

    fn clear(&mut self) {
        self.entries = [None; MAX_BUFFER_ENTRIES];
        self.count = 0;
    }

    fn is_empty(&self) -> bool {
        self.count == 0
    }

    fn len(&self) -> usize {
        self.count
    }
}

/// Verification-friendly memory backend
///
/// # Why UnsafeCell for Main Memory?
///
/// We use `UnsafeCell` instead of `RefCell` for main memory because:
/// 1. Main memory reads are frequent and should be zero-cost
/// 2. We manually guarantee safety: only one write OR multiple reads at a time
/// 3. Kani can see through `UnsafeCell` more easily than `RefCell`
///
/// The `unsafe` blocks are actually **safe** because:
/// - Kani verification mode is single-threaded
/// - We control all access patterns
/// - Rust's type system enforces `&mut self` for writes
pub struct VerificationBackend {
    /// Main memory: fixed-size array on stack
    /// TLA+: mainMemory[addr]
    ///
    /// Why UnsafeCell? Allows interior mutability for Kani's analysis
    main_memory: UnsafeCell<[Value; MAX_ADDRESSES]>,
    
    /// Per-core store buffers
    /// TLA+: storeBuffers[core]
    ///
    /// Why RefCell? Kani can model borrow checking
    store_buffers: [RefCell<BufferState>; MAX_CORES],
    
    /// Configuration (constant in verification)
    num_cores: usize,
    max_buffer_size: usize,
}

impl VerificationBackend {
    /// Create new verification backend
    pub fn new() -> Self {
        Self {
            main_memory: UnsafeCell::new([0; MAX_ADDRESSES]),
            store_buffers: [
                RefCell::new(BufferState::new()),
                RefCell::new(BufferState::new()),
            ],
            num_cores: MAX_CORES,
            max_buffer_size: MAX_BUFFER_ENTRIES,
        }
    }

    /// Create with config (enforces limits)
    pub fn with_config(num_cores: usize, max_buffer_size: usize) -> Self {
        assert!(
            num_cores <= MAX_CORES,
            "Verification mode supports max {} cores",
            MAX_CORES
        );
        assert!(
            max_buffer_size <= MAX_BUFFER_ENTRIES,
            "Verification mode supports max {} buffer entries",
            MAX_BUFFER_ENTRIES
        );

        Self::new()
    }
}

impl Default for VerificationBackend {
    fn default() -> Self {
        Self::new()
    }
}

impl MemoryBackend for VerificationBackend {
    fn read_main(&self, addr: Address) -> Value {
        if addr >= MAX_ADDRESSES {
            return 0;
        }

        // SAFETY: Single-threaded access in verification mode
        // Kani can symbolically verify this is safe
        unsafe {
            let mem = &*self.main_memory.get();
            mem[addr]
        }
    }

    fn write_main(&mut self, addr: Address, val: Value) {
        if addr >= MAX_ADDRESSES {
            return;
        }

        // SAFETY: We have &mut self, so exclusive access is guaranteed
        // Kani sees this as a simple array write
        unsafe {
            let mem = &mut *self.main_memory.get();
            mem[addr] = val;
        }
    }

    fn is_buffer_empty(&self, core: CoreId) -> bool {
        if core >= MAX_CORES {
            return true;
        }
        self.store_buffers[core].borrow().is_empty()
    }

    fn buffer_len(&self, core: CoreId) -> usize {
        if core >= MAX_CORES {
            return 0;
        }
        self.store_buffers[core].borrow().len()
    }

    fn buffer_push(&mut self, core: CoreId, entry: StoreEntry) -> Result<(), &'static str> {
        if core >= MAX_CORES {
            return Err("Invalid core ID");
        }

        // Validate address is within bounds
        if entry.addr >= MAX_ADDRESSES {
            return Err("Address out of bounds");
        }

        self.store_buffers[core].borrow_mut().push(entry)
    }

    fn buffer_pop(&mut self, core: CoreId) -> Option<StoreEntry> {
        if core >= MAX_CORES {
            return None;
        }
        self.store_buffers[core].borrow_mut().pop()
    }

    fn buffer_lookup(&self, core: CoreId, addr: Address) -> Option<Value> {
        if core >= MAX_CORES || addr >= MAX_ADDRESSES {
            return None;
        }
        self.store_buffers[core].borrow().lookup(addr)
    }

    fn clear_all(&mut self) {
        // SAFETY: Exclusive access via &mut self
        unsafe {
            let mem = &mut *self.main_memory.get();
            *mem = [0; MAX_ADDRESSES];
        }

        for buffer in &self.store_buffers {
            buffer.borrow_mut().clear();
        }
    }

    fn num_cores(&self) -> usize {
        self.num_cores
    }

    fn max_buffer_size(&self) -> usize {
        self.max_buffer_size
    }
}

impl ConfigurableBackend for VerificationBackend {
    fn with_config(num_cores: usize, max_buffer_size: usize) -> Self {
        Self::with_config(num_cores, max_buffer_size)
    }
}

// Kani verification mode is single-threaded, so this is safe
#[cfg(kani)]
unsafe impl Sync for VerificationBackend {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_verification_main_memory() {
        let mut backend = VerificationBackend::new();
        
        assert_eq!(backend.read_main(0), 0);
        
        backend.write_main(0, 100);
        assert_eq!(backend.read_main(0), 100);
    }

    #[test]
    fn test_verification_buffer_fifo() {
        let mut backend = VerificationBackend::new();
        
        backend.buffer_push(0, StoreEntry::new(0, 100)).unwrap();
        backend.buffer_push(0, StoreEntry::new(1, 200)).unwrap();
        
        // Should pop in FIFO order
        let e1 = backend.buffer_pop(0).unwrap();
        assert_eq!(e1.addr, 0);
        assert_eq!(e1.val, 100);
        
        let e2 = backend.buffer_pop(0).unwrap();
        assert_eq!(e2.addr, 1);
        assert_eq!(e2.val, 200);
    }

    #[test]
    fn test_verification_buffer_lookup() {
        let mut backend = VerificationBackend::new();
        
        backend.buffer_push(0, StoreEntry::new(0, 100)).unwrap();
        backend.buffer_push(0, StoreEntry::new(0, 200)).unwrap();
        
        // Should return most recent
        assert_eq!(backend.buffer_lookup(0, 0), Some(200));
    }

    #[test]
    fn test_verification_bounds() {
        let mut backend = VerificationBackend::new();
        
        // Out of bounds address
        assert_eq!(backend.read_main(999), 0);
        backend.write_main(999, 100); // Should not panic
        
        // Invalid core
        assert!(backend.is_buffer_empty(999));
        assert_eq!(backend.buffer_len(999), 0);
    }
}