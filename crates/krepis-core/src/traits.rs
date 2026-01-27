//! # Behavior Contracts
//!
//! Core traits that Kernel, KNUL, and Runtime implementations must satisfy.
//! Defines isolate pooling, resource guarding, and runtime lifecycle.

use crate::context::SovereignContext;
use crate::error::KrepisResult;
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

/// Resource Guard: quota and limit enforcement
///
/// Tracks and enforces per-tenant, per-request resource usage.
/// Prevents resource exhaustion attacks and ensures fair allocation.
pub trait ResourceGuard: Send + Sync {
    /// Check if operation would violate resource limits
    ///
    /// Called before executing expensive operations.
    /// Returns Ok if within limits, Err if would exceed.
    fn check_limit(&self, ctx: &SovereignContext, resource: &ResourceType) -> KrepisResult<()>;

    /// Record resource usage after operation
    ///
    /// Called after operation completes to update usage counters.
    fn record_usage(
        &self,
        ctx: &SovereignContext,
        resource: &ResourceType,
        amount: u64,
    ) -> Pin<Box<dyn Future<Output = KrepisResult<()>> + Send + '_>>;

    /// Reset quota for a tenant (typically on billing cycle boundary)
    fn reset_quota(&self, tenant_id: &str) -> Pin<Box<dyn Future<Output = KrepisResult<()>> + Send + '_>>;

    /// Get current usage for a tenant
    fn get_usage(&self, tenant_id: &str) -> ResourceUsage;
}

/// Resource types tracked by ResourceGuard
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResourceType {
    /// CPU time in microseconds
    CpuMicroseconds,
    /// Memory in bytes
    MemoryBytes,
    /// Network bandwidth in bytes
    NetworkBytes,
    /// Concurrent request count
    ConcurrentRequests,
    /// Storage in bytes
    StorageBytes,
}

impl ResourceType {
    /// Get default limit per tier
    pub fn default_limit_free(&self) -> u64 {
        match self {
            ResourceType::CpuMicroseconds => 100_000, // 100ms per request
            ResourceType::MemoryBytes => 32 * 1024 * 1024, // 32MB
            ResourceType::NetworkBytes => 10 * 1024 * 1024, // 10MB
            ResourceType::ConcurrentRequests => 5,
            ResourceType::StorageBytes => 100 * 1024 * 1024, // 100MB
        }
    }

    pub fn default_limit_pro(&self) -> u64 {
        match self {
            ResourceType::CpuMicroseconds => 1_000_000, // 1s per request
            ResourceType::MemoryBytes => 256 * 1024 * 1024, // 256MB
            ResourceType::NetworkBytes => 100 * 1024 * 1024, // 100MB
            ResourceType::ConcurrentRequests => 100,
            ResourceType::StorageBytes => 10 * 1024 * 1024 * 1024, // 10GB
        }
    }

    pub fn default_limit_enterprise(&self) -> u64 {
        match self {
            ResourceType::CpuMicroseconds => 10_000_000, // 10s per request
            ResourceType::MemoryBytes => 2 * 1024 * 1024 * 1024, // 2GB
            ResourceType::NetworkBytes => 1024 * 1024 * 1024, // 1GB
            ResourceType::ConcurrentRequests => 1000,
            ResourceType::StorageBytes => 1024 * 1024 * 1024 * 1024, // 1TB
        }
    }
}

impl std::fmt::Display for ResourceType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ResourceType::CpuMicroseconds => write!(f, "CPU"),
            ResourceType::MemoryBytes => write!(f, "Memory"),
            ResourceType::NetworkBytes => write!(f, "Network"),
            ResourceType::ConcurrentRequests => write!(f, "Concurrency"),
            ResourceType::StorageBytes => write!(f, "Storage"),
        }
    }
}

/// Current resource usage snapshot
#[derive(Debug, Clone)]
pub struct ResourceUsage {
    /// Tenant identifier
    pub tenant_id: String,
    /// CPU used in current cycle
    pub cpu_used_us: u64,
    /// Memory currently allocated
    pub memory_used_bytes: u64,
    /// Network transferred in current cycle
    pub network_used_bytes: u64,
    /// Current concurrent requests
    pub concurrent_requests: u32,
    /// Storage used
    pub storage_used_bytes: u64,
}

impl ResourceUsage {
    /// Create new usage snapshot
    pub fn new(tenant_id: impl Into<String>) -> Self {
        Self {
            tenant_id: tenant_id.into(),
            cpu_used_us: 0,
            memory_used_bytes: 0,
            network_used_bytes: 0,
            concurrent_requests: 0,
            storage_used_bytes: 0,
        }
    }

    /// Check if within free tier limits
    pub fn is_within_free_tier(&self) -> bool {
        self.cpu_used_us <= ResourceType::CpuMicroseconds.default_limit_free()
            && self.memory_used_bytes <= ResourceType::MemoryBytes.default_limit_free()
            && self.network_used_bytes <= ResourceType::NetworkBytes.default_limit_free()
            && self.concurrent_requests as u64 <= ResourceType::ConcurrentRequests.default_limit_free()
    }
}

impl Default for ResourceUsage {
    fn default() -> Self {
        Self::new("unknown")
    }
}

/// Kernel execution context and capabilities
///
/// Provided to runtime implementations to enable reverse calls into Kernel
/// (e.g., spawning child isolates, checking quotas).
pub trait KernelCapabilities: Send + Sync {
    /// Create a new child runtime instance
    fn spawn_runtime(
        &self,
        ctx: &SovereignContext,
    ) -> Pin<Box<dyn Future<Output = KrepisResult<Box<dyn SovereignRuntime>>> + Send + '_>>;

    /// Check current resource constraints
    fn check_resources(&self, ctx: &SovereignContext) -> KrepisResult<()>;

    /// Report metrics to observability system
    fn report_metrics(
        &self,
        ctx: &SovereignContext,
        metric_name: &str,
        value: f64,
    ) -> Pin<Box<dyn Future<Output = KrepisResult<()>> + Send + '_>>;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn resource_type_displays() {
        assert_eq!(ResourceType::CpuMicroseconds.to_string(), "CPU");
        assert_eq!(ResourceType::MemoryBytes.to_string(), "Memory");
    }

    #[test]
    fn resource_limits_free_tier() {
        assert_eq!(
            ResourceType::CpuMicroseconds.default_limit_free(),
            100_000
        );
        assert_eq!(ResourceType::MemoryBytes.default_limit_free(), 32 * 1024 * 1024);
    }

    #[test]
    fn runtime_stats_averaging() {
        let mut stats = RuntimeStats::new();
        stats.total_requests = 100;
        stats.total_exec_us = 500_000;
        assert_eq!(stats.avg_exec_us(), 5000.0);
    }

    #[test]
    fn resource_usage_creation() {
        let usage = ResourceUsage::new("tenant-1");
        assert_eq!(usage.tenant_id, "tenant-1");
        assert!(usage.is_within_free_tier());
    }
}