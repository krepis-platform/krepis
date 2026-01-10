//! Memory Operations
//!
//! # TLA+ Correspondence
//! Implements Read, Write, Flush operations from SimulatedMemory.tla

use super::types::{Address, CoreId, StoreEntry, Value};
use std::collections::VecDeque;

/// Store buffer for a single core
///
/// # TLA+ Correspondence
/// ```tla
/// storeBuffers: [Cores -> Seq(StoreEntry)]
/// ```
#[derive(Debug, Clone)]
pub struct StoreBuffer {
    /// Core identifier
    #[allow(dead_code)]
    core_id: CoreId,
    
    /// Buffer entries (FIFO queue)
    entries: VecDeque<StoreEntry>,
    
    /// Maximum buffer size
    max_size: usize,
}

impl StoreBuffer {
    /// Create new store buffer for core
    pub fn new(core_id: CoreId, max_size: usize) -> Self {
        Self {
            core_id,
            entries: VecDeque::with_capacity(max_size),
            max_size,
        }
    }

    /// Check if buffer is empty
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Check if buffer is full
    pub fn is_full(&self) -> bool {
        self.entries.len() >= self.max_size
    }

    /// Get current buffer size
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Add entry to buffer (FIFO tail)
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// storeBuffers' = [storeBuffers EXCEPT ![core] = Append(@, entry)]
    /// ```
    pub fn push(&mut self, entry: StoreEntry) -> Result<(), &'static str> {
        if self.is_full() {
            return Err("Store buffer full");
        }
        self.entries.push_back(entry);
        Ok(())
    }

    /// Remove oldest entry from buffer (FIFO head)
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// storeBuffers' = [storeBuffers EXCEPT ![core] = Tail(@)]
    /// ```
    pub fn pop(&mut self) -> Option<StoreEntry> {
        self.entries.pop_front()
    }

    /// Lookup most recent value for address in buffer
    ///
    /// # TLA+ Correspondence
    /// ```tla
    /// BufferLookup(core, addr) ==
    ///     LET buf == storeBuffers[core]
    ///         matching == {i \in 1..Len(buf) : buf[i].addr = addr}
    ///     IN  IF matching = {} THEN "NONE"
    ///         ELSE buf[CHOOSE x \in matching : \A y \in matching : x >= y].val
    /// ```
    pub fn lookup(&self, addr: Address) -> Option<Value> {
        // Search from newest to oldest
        self.entries.iter().rev()
            .find(|entry| entry.addr == addr)
            .map(|entry| entry.val)
    }

    /// Clear all entries
    pub fn clear(&mut self) {
        self.entries.clear();
    }

    /// Get all entries (for inspection)
    pub fn entries(&self) -> &VecDeque<StoreEntry> {
        &self.entries
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_store_buffer_push_pop() {
        let mut buf = StoreBuffer::new(0, 2);
        
        assert!(buf.is_empty());
        
        buf.push(StoreEntry::new(10, 100)).unwrap();
        buf.push(StoreEntry::new(20, 200)).unwrap();
        
        assert!(buf.is_full());
        assert!(buf.push(StoreEntry::new(30, 300)).is_err());
        
        let entry1 = buf.pop().unwrap();
        assert_eq!(entry1.addr, 10);
        assert_eq!(entry1.val, 100);
        
        let entry2 = buf.pop().unwrap();
        assert_eq!(entry2.addr, 20);
        assert_eq!(entry2.val, 200);
        
        assert!(buf.is_empty());
    }

    #[test]
    fn test_buffer_lookup() {
        let mut buf = StoreBuffer::new(0, 4);
        
        buf.push(StoreEntry::new(10, 100)).unwrap();
        buf.push(StoreEntry::new(20, 200)).unwrap();
        buf.push(StoreEntry::new(10, 300)).unwrap(); // Overwrite addr 10
        
        // Should return most recent value for addr 10
        assert_eq!(buf.lookup(10), Some(300));
        assert_eq!(buf.lookup(20), Some(200));
        assert_eq!(buf.lookup(99), None);
    }

    #[test]
    fn test_buffer_clear() {
        let mut buf = StoreBuffer::new(0, 2);
        
        buf.push(StoreEntry::new(10, 100)).unwrap();
        buf.push(StoreEntry::new(20, 200)).unwrap();
        
        buf.clear();
        
        assert!(buf.is_empty());
        assert_eq!(buf.len(), 0);
    }
}