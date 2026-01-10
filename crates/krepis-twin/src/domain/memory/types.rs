//! Simulated Memory Types
//!
//! # TLA+ Correspondence
//! Types from SimulatedMemory.tla specification

use std::fmt;

/// Memory address
///
/// # TLA+ Correspondence
/// Element of `Addresses` set
pub type Address = usize;

/// Memory value
///
/// # TLA+ Correspondence
/// Element of `Values` set
pub type Value = u64;

/// CPU Core identifier
///
/// # TLA+ Correspondence
/// Element of `Cores` set (1..NumCores)
pub type CoreId = usize;

/// Store buffer entry
///
/// # TLA+ Correspondence
/// ```tla
/// [addr: Address, val: Value]
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StoreEntry {
    /// Memory address
    pub addr: Address,
    /// Value to write
    pub val: Value,
}

impl StoreEntry {
    /// initialize.
    pub fn new(addr: Address, val: Value) -> Self {
        Self { addr, val }
    }
}

/// Memory operation type
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemoryOp {
    /// Read from address
    Read {
        /// Core performing read
        core: CoreId,
        /// Address to read
        addr: Address,
    },
    /// Write to address (buffered)
    Write {
        /// Core performing write
        core: CoreId,
        /// Address to write
        addr: Address,
        /// Value to write
        val: Value,
    },
    /// Memory fence (flush store buffer)
    Fence {
        /// Core issuing fence
        core: CoreId,
    },
}

/// Memory consistency model
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConsistencyModel {
    /// Sequential consistency
    SequentiallyConsistent,
    /// Relaxed (with store buffers)
    Relaxed,
}

/// Memory configuration
#[derive(Debug, Clone)]
pub struct MemoryConfig {
    /// Number of CPU cores
    pub num_cores: usize,
    
    /// Maximum store buffer size per core
    pub max_buffer_size: usize,
    
    /// Memory consistency model
    pub consistency_model: ConsistencyModel,
    
    /// Initial memory size (number of addressable locations)
    pub initial_size: usize,
}

impl Default for MemoryConfig {
    fn default() -> Self {
        Self {
            num_cores: 2,
            max_buffer_size: 2, // TLA+ spec uses 2
            consistency_model: ConsistencyModel::Relaxed,
            initial_size: 1024,
        }
    }
}

impl fmt::Display for MemoryOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MemoryOp::Read { core, addr } => {
                write!(f, "Read(core={}, addr={})", core, addr)
            }
            MemoryOp::Write { core, addr, val } => {
                write!(f, "Write(core={}, addr={}, val={})", core, addr, val)
            }
            MemoryOp::Fence { core } => {
                write!(f, "Fence(core={})", core)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_store_entry_creation() {
        let entry = StoreEntry::new(42, 100);
        assert_eq!(entry.addr, 42);
        assert_eq!(entry.val, 100);
    }

    #[test]
    fn test_memory_config_default() {
        let config = MemoryConfig::default();
        assert_eq!(config.num_cores, 2);
        assert_eq!(config.max_buffer_size, 2);
    }
}