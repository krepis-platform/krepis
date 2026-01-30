//! Resource Domain
//!
//! Defines resource quota enforcement, usage tracking, and tier-based limits
//! that prevent resource exhaustion attacks and ensure fair allocation across
//! multiple tenants.

use crate::domain::{KrepisResult, SovereignContext};
use std::future::Future;
use std::pin::Pin;

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
    fn resource_usage_creation() {
        let usage = ResourceUsage::new("tenant-1");
        assert_eq!(usage.tenant_id, "tenant-1");
        assert!(usage.is_within_free_tier());
    }

    #[test]
    fn resource_limits_pro() {
        assert_eq!(
            ResourceType::CpuMicroseconds.default_limit_pro(),
            1_000_000
        );
    }

    #[test]
    fn resource_limits_enterprise() {
        assert_eq!(
            ResourceType::MemoryBytes.default_limit_enterprise(),
            2 * 1024 * 1024 * 1024
        );
    }
}