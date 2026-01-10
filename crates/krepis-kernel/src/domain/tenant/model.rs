//! Domain Model: Tenant Metadata and Resource Configuration
//! 
//! Core domain entities representing tenant identity and resource quotas.
//! No infrastructure dependencies - pure business data and logic.

use serde::{Deserialize, Serialize};
use std::time::Duration;

use super::tier::TenantTier;
use super::error::TenantError;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Resource Configuration
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/// Resource quotas and execution limits for a tenant tier
/// 
/// This is pure data - no enforcement logic here.
/// The adapters layer reads these values to configure runtime behavior.
/// 
/// # Spec Compliance
/// 
/// - Sovereign-003: Tier-based resource allocation
/// - Performance: Turbo flag determines execution path (FFI vs shared memory)
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ResourceConfig {
    /// Maximum concurrent requests per tenant
    /// 
    /// Enforced by Bulkhead pattern (C-002) in adapters layer
    pub max_concurrent_requests: usize,

    /// Maximum execution time per request
    /// 
    /// Enforced by Watchdog (C-003) in adapters layer
    pub max_execution_time: Duration,

    /// Memory limit in megabytes
    /// 
    /// To be enforced by V8 heap limits (future)
    pub max_memory_mb: u64,

    /// CPU time limit in milliseconds
    /// 
    /// To be enforced by accounting and throttling (future)
    pub max_cpu_time_ms: u64,

    /// **Turbo Acceleration Flag**
    /// 
    /// When true, this tenant qualifies for zero-copy shared memory execution.
    /// The adapters layer uses this to route to ContextStorage::Turbo.
    /// 
    /// # Performance Impact
    /// 
    /// - `false`: ~41.5µs context sync via Protobuf FFI
    /// - `true`: <500ns context sync via shared memory
    pub use_turbo_acceleration: bool,

    /// Sentinel AI monitoring enabled
    /// 
    /// When true, execution anomalies are sent to Sentinel AI for analysis.
    /// Only available for Enterprise tier.
    pub sentinel_monitoring: bool,
}

impl ResourceConfig {
    /// Get resource configuration for a specific tier
    /// 
    /// # Design Note
    /// 
    /// This is the single source of truth for tier quotas.
    /// All changes to tier limits should be made here.
    /// 
    /// # Arguments
    /// 
    /// * `tier` - Tenant tier to get configuration for
    /// 
    /// # Returns
    /// 
    /// Resource configuration matching the tier's capabilities
    pub fn for_tier(tier: TenantTier) -> Self {
        match tier {
            TenantTier::Free => Self {
                max_concurrent_requests: 5,
                max_execution_time: Duration::from_millis(100),
                max_memory_mb: 128,
                max_cpu_time_ms: 100,
                use_turbo_acceleration: false,
                sentinel_monitoring: false,
            },

            TenantTier::Standard => Self {
                max_concurrent_requests: 20,
                max_execution_time: Duration::from_millis(500),
                max_memory_mb: 512,
                max_cpu_time_ms: 500,
                use_turbo_acceleration: false,
                sentinel_monitoring: false,
            },

            TenantTier::Turbo => Self {
                max_concurrent_requests: 100,
                max_execution_time: Duration::from_millis(2000),
                max_memory_mb: 2048,
                max_cpu_time_ms: 2000,
                use_turbo_acceleration: true, // ⚡ Turbo acceleration enabled
                sentinel_monitoring: false,
            },

            TenantTier::Pro => Self {
                max_concurrent_requests: 500,
                max_execution_time: Duration::from_millis(10_000),
                max_memory_mb: 8192,
                max_cpu_time_ms: 10_000,
                use_turbo_acceleration: true, // ⚡ Turbo acceleration enabled
                sentinel_monitoring: false,
            },

            TenantTier::Enterprise => Self {
                max_concurrent_requests: usize::MAX, // Effectively unlimited
                max_execution_time: Duration::from_millis(60_000),
                max_memory_mb: u64::MAX, // Effectively unlimited
                max_cpu_time_ms: u64::MAX,
                use_turbo_acceleration: true, // ⚡ Turbo acceleration enabled
                sentinel_monitoring: true,   // 🛡️ Sentinel AI monitoring
            },
        }
    }

    /// Check if this configuration allows Turbo acceleration
    /// 
    /// # Returns
    /// 
    /// `true` if zero-copy shared memory is enabled
    #[inline]
    pub fn is_turbo_enabled(&self) -> bool {
        self.use_turbo_acceleration
    }

    /// Check if this configuration has Sentinel monitoring
    /// 
    /// # Returns
    /// 
    /// `true` if Sentinel AI monitoring is enabled
    #[inline]
    pub fn is_sentinel_enabled(&self) -> bool {
        self.sentinel_monitoring
    }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Tenant Metadata
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/// Tenant domain entity
/// 
/// Represents a single tenant with their identity, tier, and resource configuration.
/// 
/// # Spec Compliance
/// 
/// - Sovereign-002: Tenant context identification
/// - Sovereign-003: Resource quota management
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TenantMetadata {
    /// Unique tenant identifier (UUID string)
    pub tenant_id: String,

    /// Current subscription tier
    tier: TenantTier,

    /// Cached resource configuration for this tier
    #[serde(skip)]
    resource_config: ResourceConfig,

    /// Tenant active status
    /// 
    /// Inactive tenants (suspended, banned, unpaid) cannot execute code
    pub active: bool,

    /// Creation timestamp (milliseconds since UNIX epoch)
    pub created_at: i64,

    /// Storage tree name for Sled DB isolation
    /// 
    /// Format: `tenant_db_{tenant_id}`
    pub storage_tree: String,

    /// Virtual filesystem root for path remapping
    /// 
    /// Format: `root/tenants/{tenant_id}`
    pub fs_root: String,
}

impl TenantMetadata {
    /// Create new tenant metadata
    /// 
    /// # Arguments
    /// 
    /// * `tenant_id` - Unique tenant identifier
    /// * `tier` - Initial subscription tier
    /// 
    /// # Returns
    /// 
    /// New tenant metadata with default values
    pub fn new(tenant_id: String, tier: TenantTier) -> Self {
        Self {
            storage_tree: format!("tenant_db_{}", tenant_id),
            fs_root: format!("root/tenants/{}", tenant_id),
            tenant_id,
            tier,
            resource_config: ResourceConfig::for_tier(tier),
            active: true,
            created_at: crate::domain::now_ms(),
        }
    }

    /// Get tenant tier
    /// 
    /// # Returns
    /// 
    /// Current subscription tier
    #[inline]
    pub fn tier(&self) -> TenantTier {
        self.tier
    }

    /// Get resource configuration
    /// 
    /// # Returns
    /// 
    /// Reference to cached resource configuration
    #[inline]
    pub fn resource_config(&self) -> &ResourceConfig {
        &self.resource_config
    }

    /// Check if tenant should use Turbo acceleration
    /// 
    /// # Returns
    /// 
    /// `true` if zero-copy shared memory should be used
    #[inline]
    pub fn uses_turbo(&self) -> bool {
        self.resource_config.use_turbo_acceleration
    }

    /// Check if tenant has Sentinel monitoring
    /// 
    /// # Returns
    /// 
    /// `true` if Sentinel AI monitoring is enabled
    #[inline]
    pub fn has_sentinel(&self) -> bool {
        self.resource_config.sentinel_monitoring
    }

    /// Upgrade tenant tier
    /// 
    /// # Business Rule
    /// 
    /// Tier can only be upgraded, never downgraded in production.
    /// Downgrades require manual intervention for billing reasons.
    /// 
    /// # Arguments
    /// 
    /// * `new_tier` - Target tier to upgrade to
    /// 
    /// # Returns
    /// 
    /// `Ok(())` if upgrade successful, `Err(TenantError)` if invalid
    pub fn upgrade_tier(&mut self, new_tier: TenantTier) -> Result<(), TenantError> {
        if !self.tier.can_upgrade_to(new_tier) {
            return Err(TenantError::InvalidTierChange {
                current: self.tier,
                requested: new_tier,
            });
        }

        self.tier = new_tier;
        self.resource_config = ResourceConfig::for_tier(new_tier);

        Ok(())
    }

    /// Validate tenant state
    /// 
    /// # Business Rule
    /// 
    /// Inactive tenants cannot execute code.
    /// 
    /// # Returns
    /// 
    /// `Ok(())` if valid, `Err(TenantError)` if inactive
    pub fn validate(&self) -> Result<(), TenantError> {
        if !self.active {
            return Err(TenantError::Inactive(self.tenant_id.clone()));
        }

        Ok(())
    }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Tests
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_resource_config_for_tier() {
        let free_config = ResourceConfig::for_tier(TenantTier::Free);
        assert!(!free_config.use_turbo_acceleration);
        assert!(!free_config.sentinel_monitoring);
        assert_eq!(free_config.max_concurrent_requests, 5);
        assert_eq!(free_config.max_memory_mb, 128);

        let turbo_config = ResourceConfig::for_tier(TenantTier::Turbo);
        assert!(turbo_config.use_turbo_acceleration);
        assert!(!turbo_config.sentinel_monitoring);
        assert_eq!(turbo_config.max_concurrent_requests, 100);
        assert_eq!(turbo_config.max_memory_mb, 2048);

        let enterprise_config = ResourceConfig::for_tier(TenantTier::Enterprise);
        assert!(enterprise_config.use_turbo_acceleration);
        assert!(enterprise_config.sentinel_monitoring);
        assert_eq!(enterprise_config.max_concurrent_requests, usize::MAX);
    }

    #[test]
    fn test_resource_config_turbo_checks() {
        let free_config = ResourceConfig::for_tier(TenantTier::Free);
        assert!(!free_config.is_turbo_enabled());
        assert!(!free_config.is_sentinel_enabled());

        let enterprise_config = ResourceConfig::for_tier(TenantTier::Enterprise);
        assert!(enterprise_config.is_turbo_enabled());
        assert!(enterprise_config.is_sentinel_enabled());
    }

    #[test]
    fn test_tenant_metadata_creation() {
        let tenant = TenantMetadata::new("test-123".to_string(), TenantTier::Free);

        assert_eq!(tenant.tenant_id, "test-123");
        assert_eq!(tenant.tier(), TenantTier::Free);
        assert_eq!(tenant.storage_tree, "tenant_db_test-123");
        assert_eq!(tenant.fs_root, "root/tenants/test-123");
        assert!(tenant.active);
        assert!(!tenant.uses_turbo());
        assert!(!tenant.has_sentinel());
    }

    #[test]
    fn test_tenant_turbo_flags() {
        let free_tenant = TenantMetadata::new("free".to_string(), TenantTier::Free);
        assert!(!free_tenant.uses_turbo());

        let turbo_tenant = TenantMetadata::new("turbo".to_string(), TenantTier::Turbo);
        assert!(turbo_tenant.uses_turbo());
        assert!(!turbo_tenant.has_sentinel());

        let enterprise_tenant = TenantMetadata::new("ent".to_string(), TenantTier::Enterprise);
        assert!(enterprise_tenant.uses_turbo());
        assert!(enterprise_tenant.has_sentinel());
    }

    #[test]
    fn test_tenant_tier_upgrade() {
        let mut tenant = TenantMetadata::new("test".to_string(), TenantTier::Free);

        // Valid upgrade
        assert!(tenant.upgrade_tier(TenantTier::Turbo).is_ok());
        assert_eq!(tenant.tier(), TenantTier::Turbo);
        assert!(tenant.uses_turbo());

        // Invalid downgrade
        let result = tenant.upgrade_tier(TenantTier::Standard);
        assert!(result.is_err());
        assert_eq!(tenant.tier(), TenantTier::Turbo); // Unchanged

        // Cannot upgrade to same tier
        let result = tenant.upgrade_tier(TenantTier::Turbo);
        assert!(result.is_err());
    }

    #[test]
    fn test_tenant_validation() {
        let mut tenant = TenantMetadata::new("test".to_string(), TenantTier::Standard);

        // Active tenant is valid
        assert!(tenant.validate().is_ok());

        // Inactive tenant is invalid
        tenant.active = false;
        let result = tenant.validate();
        assert!(result.is_err());
        match result.unwrap_err() {
            TenantError::Inactive(id) => assert_eq!(id, "test"),
            _ => panic!("Expected Inactive error"),
        }
    }

    #[test]
    fn test_tenant_resource_config_sync() {
        let mut tenant = TenantMetadata::new("test".to_string(), TenantTier::Free);

        // Initial config for Free tier
        assert_eq!(tenant.resource_config().max_concurrent_requests, 5);

        // Upgrade to Turbo
        tenant.upgrade_tier(TenantTier::Turbo).unwrap();

        // Config should be updated
        assert_eq!(tenant.resource_config().max_concurrent_requests, 100);
        assert!(tenant.resource_config().use_turbo_acceleration);
    }

    #[test]
    fn test_tenant_serialization() {
        let tenant = TenantMetadata::new("test-456".to_string(), TenantTier::Turbo);

        let json = serde_json::to_string(&tenant).unwrap();
        assert!(json.contains("test-456"));
        assert!(json.contains("Turbo") || json.contains("2"));

        let deserialized: TenantMetadata = serde_json::from_str(&json).unwrap();
        assert_eq!(deserialized.tenant_id, "test-456");
        assert_eq!(deserialized.tier(), TenantTier::Turbo);
    }
}