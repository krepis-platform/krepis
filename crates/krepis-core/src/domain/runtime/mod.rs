//! Runtime Domain
//!
//! Defines the contract for execution runtimes (isolate pools, WASM engines, etc.)
//! that the Krepis kernel manages for executing user workloads with resource limits
//! and lifecycle guarantees.

use crate::domain::{KrepisResult, SovereignContext};
use std::future::Future;
use std::pin::Pin;

/// Sovereign Runtime lifecycle contract
///
/// Defines the contract that all Krepis runtimes (V8 isolate pools, WASM runtimes, etc.)
/// must implement for the Kernel to manage execution and resource constraints.
pub trait SovereignRuntime: Send + Sync {
    /// Initialize runtime with given context
    ///
    /// Called once per runtime instance. Must set up isolate pools,
    /// memory limits, and internal state tracking.
    fn init(
        &self,
        ctx: &SovereignContext,
    ) -> Pin<Box<dyn Future<Output = KrepisResult<()>> + Send + '_>>;

    /// Execute workload in the runtime
    ///
    /// Receives serialized code/request, executes in a managed isolate,
    /// and returns serialized result.
    fn execute(
        &self,
        ctx: &SovereignContext,
        payload: &[u8],
    ) -> Pin<Box<dyn Future<Output = KrepisResult<Vec<u8>>> + Send + '_>>;

    /// Terminate runtime gracefully
    ///
    /// Called when runtime should shut down. Must clean up resources,
    /// drain pending operations, and release memory.
    fn terminate(
        &self,
        ctx: &SovereignContext,
    ) -> Pin<Box<dyn Future<Output = KrepisResult<()>> + Send + '_>>;

    /// Check if runtime is ready for requests
    fn is_ready(&self) -> bool;

    /// Get current resource usage snapshot
    fn get_stats(&self) -> RuntimeStats;
}

/// Runtime statistics snapshot
#[derive(Debug, Clone)]
pub struct RuntimeStats {
    /// Total isolates in pool
    pub isolate_count: u32,
    /// Currently active isolates
    pub active_isolates: u32,
    /// Current heap usage in bytes
    pub heap_bytes: u64,
    /// Total requests processed
    pub total_requests: u64,
    /// Requests currently in-flight
    pub pending_requests: u32,
    /// Total execution time in microseconds
    pub total_exec_us: u64,
}

impl RuntimeStats {
    /// Create empty stats
    pub fn new() -> Self {
        Self {
            isolate_count: 0,
            active_isolates: 0,
            heap_bytes: 0,
            total_requests: 0,
            pending_requests: 0,
            total_exec_us: 0,
        }
    }

    /// Calculate average execution time
    pub fn avg_exec_us(&self) -> f64 {
        if self.total_requests == 0 {
            0.0
        } else {
            self.total_exec_us as f64 / self.total_requests as f64
        }
    }
}

impl Default for RuntimeStats {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn runtime_stats_creation() {
        let stats = RuntimeStats::new();
        assert_eq!(stats.isolate_count, 0);
        assert_eq!(stats.total_requests, 0);
    }

    #[test]
    fn runtime_stats_averaging() {
        let mut stats = RuntimeStats::new();
        stats.total_requests = 100;
        stats.total_exec_us = 500_000;
        assert_eq!(stats.avg_exec_us(), 5000.0);
    }

    #[test]
    fn runtime_stats_default() {
        let stats = RuntimeStats::default();
        assert_eq!(stats.isolate_count, 0);
    }
}