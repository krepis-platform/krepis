//! Production Memory Backend - Maximum Performance
//!
//! # Design for Production
//!
//! This backend is engineered for **real-world concurrent workloads**:
//! - `DashMap` for lock-free concurrent main memory access
//! - `Vec<RwLock<StoreBuffer>>` for per-core store buffers
//! - Dynamic heap allocation for unlimited capacity
//!
//! # Why Kani Hates This
//! - DashMap uses complex lock-free algorithms → Kani can't model atomic ops
//! - RwLock requires OS syscalls → Kani can't see into kernel
//! - Heap allocation is unbounded → infinite state space
//!
//! But we don't care! This is for production, not verification.

use super::backend::{ConfigurableBackend, MemoryBackend};
use super::ops::StoreBuffer;
use super::types::{Address, CoreId, StoreEntry, Value};
#[cfg(not(kani))]
use dashmap::DashMap;
use parking_lot::RwLock;

/// Production-grade memory backend
///
/// # Memory Layout
/// ```text
/// ProductionBackend
/// ├─ main_memory: DashMap<Address, Value>  (concurrent hashmap)
/// ├─ store_buffers: Vec<RwLock<StoreBuffer>>
/// │   ├─ [0]: RwLock<StoreBuffer>  (Core 0's buffer)
/// │   ├─ [1]: RwLock<StoreBuffer>  (Core 1's buffer)
/// │   └─ ...
/// ├─ num_cores: usize
/// └─ max_buffer_size: usize
/// ```
///
/// # Thread Safety
/// - `DashMap` allows concurrent reads and writes without external locking
/// - `RwLock` protects each store buffer individually
/// - Multiple cores can write to different buffers simultaneously
pub struct ProductionBackend {
    /// Main memory: concurrent hashmap for O(1) lookups
    /// TLA+: mainMemory[addr]
    main_memory: DashMap<Address, Value>,
    
    /// Per-core store buffers (FIFO queues)
    /// TLA+: storeBuffers[core]
    store_buffers: Vec<RwLock<StoreBuffer>>,
    
    /// Configuration
    num_cores: usize,
    max_buffer_size: usize,
}

impl ProductionBackend {
    /// Create new production backend
    pub fn new(num_cores: usize, max_buffer_size: usize) -> Self {
        let store_buffers = (0..num_cores)
            .map(|core_id| RwLock::new(StoreBuffer::new(core_id, max_buffer_size)))
            .collect();

        Self {
            main_memory: DashMap::new(),
            store_buffers,
            num_cores,
            max_buffer_size,
        }
    }
}

impl MemoryBackend for ProductionBackend {
    fn read_main(&self, addr: Address) -> Value {
        // DashMap::get returns a smart pointer (Ref)
        // We dereference it to get the value
        self.main_memory
            .get(&addr)
            .map(|r| *r)
            .unwrap_or(0)
    }

    fn write_main(&mut self, addr: Address, val: Value) {
        // DashMap::insert is atomic and lock-free
        self.main_memory.insert(addr, val);
    }

    fn is_buffer_empty(&self, core: CoreId) -> bool {
        if core >= self.num_cores {
            return true;
        }
        self.store_buffers[core].read().is_empty()
    }

    fn buffer_len(&self, core: CoreId) -> usize {
        if core >= self.num_cores {
            return 0;
        }
        self.store_buffers[core].read().len()
    }

    fn buffer_push(&mut self, core: CoreId, entry: StoreEntry) -> Result<(), &'static str> {
        if core >= self.num_cores {
            return Err("Invalid core ID");
        }
        
        // Acquire write lock on this core's buffer
        self.store_buffers[core].write().push(entry)
    }

    fn buffer_pop(&mut self, core: CoreId) -> Option<StoreEntry> {
        if core >= self.num_cores {
            return None;
        }
        
        // FIFO: pop from head
        self.store_buffers[core].write().pop()
    }

    fn buffer_lookup(&self, core: CoreId, addr: Address) -> Option<Value> {
        if core >= self.num_cores {
            return None;
        }
        
        // Search from newest to oldest (reverse order for forwarding)
        self.store_buffers[core].read().lookup(addr)
    }

    fn clear_all(&mut self) {
        self.main_memory.clear();
        for buffer in &self.store_buffers {
            buffer.write().clear();
        }
    }

    fn num_cores(&self) -> usize {
        self.num_cores
    }

    fn max_buffer_size(&self) -> usize {
        self.max_buffer_size
    }
}

impl ConfigurableBackend for ProductionBackend {
    fn with_config(num_cores: usize, max_buffer_size: usize) -> Self {
        Self::new(num_cores, max_buffer_size)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_production_main_memory() {
        let mut backend = ProductionBackend::new(2, 2);
        
        assert_eq!(backend.read_main(42), 0);
        
        backend.write_main(42, 100);
        assert_eq!(backend.read_main(42), 100);
    }

    #[test]
    fn test_production_store_buffer() {
        let mut backend = ProductionBackend::new(2, 2);
        
        assert!(backend.is_buffer_empty(0));
        
        backend.buffer_push(0, StoreEntry::new(10, 100)).unwrap();
        assert!(!backend.is_buffer_empty(0));
        assert_eq!(backend.buffer_len(0), 1);
        
        let entry = backend.buffer_pop(0).unwrap();
        assert_eq!(entry.addr, 10);
        assert_eq!(entry.val, 100);
    }

    #[test]
    fn test_production_buffer_lookup() {
        let mut backend = ProductionBackend::new(2, 2);
        
        backend.buffer_push(0, StoreEntry::new(10, 100)).unwrap();
        backend.buffer_push(0, StoreEntry::new(10, 200)).unwrap();
        
        // Should return most recent value
        assert_eq!(backend.buffer_lookup(0, 10), Some(200));
    }
}