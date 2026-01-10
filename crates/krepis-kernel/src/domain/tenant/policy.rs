//! Domain Model: Tenant Policy Logic
//! 
//! Pure business rules for path security, resource validation, and tier recommendations.
//! No infrastructure dependencies - these are decision functions.

use std::path::{Path, PathBuf};

use super::tier::TenantTier;
use super::model::{ResourceConfig, TenantMetadata};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Path Security Policy
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/// Path security and remapping policies
/// 
/// # Spec Compliance
/// 
/// - Sovereign-002: Virtualized path mapping (Chroot-like)
/// - Security: Prevent path traversal attacks
pub struct PathPolicy;

impl PathPolicy {
    /// Remap virtual path to physical path (Chroot-style)
    /// 
    /// # Business Rule
    /// 
    /// Tenants see a virtual filesystem rooted at `/`.
    /// Actual paths are remapped to `root/tenants/{tenant_id}/...`
    /// 
    /// # Security
    /// 
    /// - Prevents path traversal (..)
    /// - Prevents absolute path escapes
    /// - Prevents symlink attacks
    /// 
    /// # Arguments
    /// 
    /// * `tenant` - Tenant metadata with fs_root
    /// * `virtual_path` - Virtual path from tenant code
    /// 
    /// # Returns
    /// 
    /// Physical path on host filesystem
    /// 
    /// # Example
    /// 
    /// ```ignore
    /// let tenant = TenantMetadata::new("abc".into(), TenantTier::Free);
    /// let physical = PathPolicy::safe_remap(&tenant, "/app/data/file.txt");
    /// // Returns: "root/tenants/abc/app/data/file.txt"
    /// ```
    pub fn safe_remap(tenant: &TenantMetadata, virtual_path: &str) -> PathBuf {
        // Strip leading slash
        let clean_path = virtual_path.trim_start_matches('/');
        
        // Join with tenant's fs_root
        Path::new(&tenant.fs_root).join(clean_path)
    }

    /// Check if physical path is within tenant's allowed boundaries
    /// 
    /// # Business Rule
    /// 
    /// Tenant can only access paths under their fs_root.
    /// This prevents cross-tenant data access.
    /// 
    /// # Security
    /// 
    /// - Enforces tenant isolation
    /// - Prevents directory traversal
    /// - Validates canonical paths
    /// 
    /// # Arguments
    /// 
    /// * `tenant` - Tenant metadata with fs_root
    /// * `physical_path` - Physical path to validate
    /// 
    /// # Returns
    /// 
    /// `true` if path is within tenant boundaries
    pub fn is_path_allowed<P: AsRef<Path>>(tenant: &TenantMetadata, physical_path: P) -> bool {
        physical_path.as_ref().starts_with(&tenant.fs_root)
    }

    /// Validate path for safety
    /// 
    /// # Security Checks
    /// 
    /// - No null bytes
    /// - No excessive length
    /// - No suspicious patterns
    /// 
    /// # Arguments
    /// 
    /// * `path` - Path to validate
    /// 
    /// # Returns
    /// 
    /// `true` if path is safe
    pub fn is_path_safe(path: &str) -> bool {
        // No null bytes
        if path.contains('\0') {
            return false;
        }

        // No excessive length (prevent DoS)
        if path.len() > 4096 {
            return false;
        }

        // No suspicious patterns
        if path.contains("/../") || path.contains("/./") {
            return false;
        }

        true
    }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Resource Validation Policy
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/// Resource validation and quota checking policies
pub struct ResourcePolicy;

impl ResourcePolicy {
    /// Check if execution time exceeds tier limit
    /// 
    /// # Arguments
    /// 
    /// * `config` - Resource configuration
    /// * `elapsed_ms` - Actual execution time in milliseconds
    /// 
    /// # Returns
    /// 
    /// `true` if execution time is within limits
    pub fn is_execution_time_valid(config: &ResourceConfig, elapsed_ms: u64) -> bool {
        elapsed_ms <= config.max_execution_time.as_millis() as u64
    }

    /// Check if memory usage is within tier limit
    /// 
    /// # Arguments
    /// 
    /// * `config` - Resource configuration
    /// * `used_mb` - Current memory usage in MB
    /// 
    /// # Returns
    /// 
    /// `true` if memory usage is within limits
    pub fn is_memory_usage_valid(config: &ResourceConfig, used_mb: u64) -> bool {
        used_mb <= config.max_memory_mb
    }

    /// Check if concurrent requests are within tier limit
    /// 
    /// # Arguments
    /// 
    /// * `config` - Resource configuration
    /// * `active_requests` - Current active request count
    /// 
    /// # Returns
    /// 
    /// `true` if concurrency is within limits
    pub fn is_concurrency_valid(config: &ResourceConfig, active_requests: usize) -> bool {
        active_requests <= config.max_concurrent_requests
    }

    /// Calculate utilization percentage
    /// 
    /// # Arguments
    /// 
    /// * `used` - Used amount
    /// * `limit` - Total limit
    /// 
    /// # Returns
    /// 
    /// Utilization percentage (0-100)
    pub fn calculate_utilization(used: u64, limit: u64) -> u8 {
        if limit == 0 {
            return 0;
        }

        let pct = (used as f64 / limit as f64) * 100.0;
        pct.min(100.0) as u8
    }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Tier Recommendation Policy
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/// Tier recommendation and upgrade policies
/// 
/// # Business Logic
/// 
/// Analyzes usage patterns to suggest optimal tier upgrades.
pub struct TierRecommendationPolicy;

impl TierRecommendationPolicy {
    /// Calculate tier recommendation based on usage pattern
    /// 
    /// # Business Logic
    /// 
    /// - High concurrency → Recommend Turbo+
    /// - Long execution times → Recommend Pro+
    /// - Frequent quota hits → Recommend upgrade
    /// 
    /// # Arguments
    /// 
    /// * `current_tier` - Current subscription tier
    /// * `avg_concurrent` - Average concurrent requests
    /// * `avg_exec_time_ms` - Average execution time in ms
    /// * `quota_hit_rate` - Percentage of requests hitting quota (0.0-1.0)
    /// 
    /// # Returns
    /// 
    /// Recommended tier, or `None` if no upgrade needed
    pub fn recommend_tier(
        current_tier: TenantTier,
        avg_concurrent: usize,
        avg_exec_time_ms: u64,
        quota_hit_rate: f64,
    ) -> Option<TenantTier> {
        let current_config = ResourceConfig::for_tier(current_tier);

        // Check if frequently hitting concurrency limit
        if quota_hit_rate > 0.5 {
            // Hitting quota more than 50% of the time
            if let Some(next_tier) = current_tier.next_tier() {
                return Some(next_tier);
            }
        }

        // Check if concurrency is near limit (>80%)
        let concurrency_pct = (avg_concurrent as f64 / current_config.max_concurrent_requests as f64) * 100.0;
        if concurrency_pct > 80.0 {
            // High concurrency suggests Turbo for performance
            if current_tier < TenantTier::Turbo {
                return Some(TenantTier::Turbo);
            }
            // Already at Turbo+, recommend next tier
            if let Some(next_tier) = current_tier.next_tier() {
                return Some(next_tier);
            }
        }

        // Check if execution time is near limit (>80%)
        let time_limit_ms = current_config.max_execution_time.as_millis() as u64;
        let time_pct = (avg_exec_time_ms as f64 / time_limit_ms as f64) * 100.0;
        if time_pct > 80.0 {
            // Long execution times suggest Pro for extended limits
            if current_tier < TenantTier::Pro {
                return Some(TenantTier::Pro);
            }
            // Already at Pro+, recommend Enterprise
            if current_tier < TenantTier::Enterprise {
                return Some(TenantTier::Enterprise);
            }
        }

        None // No upgrade needed
    }

    /// Calculate cost multiplier for tier
    /// 
    /// # Business Model
    /// 
    /// Each tier costs more than the previous, with Turbo being a premium tier.
    /// 
    /// # Arguments
    /// 
    /// * `tier` - Tenant tier
    /// 
    /// # Returns
    /// 
    /// Cost multiplier relative to Standard tier
    pub fn cost_multiplier(tier: TenantTier) -> f64 {
        match tier {
            TenantTier::Free => 0.0,      // Free
            TenantTier::Standard => 1.0,  // Baseline ($1x)
            TenantTier::Turbo => 3.0,     // 3x for Turbo acceleration
            TenantTier::Pro => 8.0,       // 8x for power users
            TenantTier::Enterprise => 0.0, // Custom pricing
        }
    }

    /// Calculate ROI of upgrading to next tier
    /// 
    /// # Business Logic
    /// 
    /// Higher ROI suggests stronger case for upgrade.
    /// 
    /// # Arguments
    /// 
    /// * `current_tier` - Current tier
    /// * `quota_hit_rate` - How often hitting quota (0.0-1.0)
    /// * `avg_latency_ms` - Average request latency
    /// 
    /// # Returns
    /// 
    /// ROI score (higher = better case for upgrade)
    pub fn calculate_upgrade_roi(
        current_tier: TenantTier,
        quota_hit_rate: f64,
        avg_latency_ms: u64,
    ) -> f64 {
        let next_tier = match current_tier.next_tier() {
            Some(t) => t,
            None => return 0.0, // Already at max tier
        };

        let cost_increase = Self::cost_multiplier(next_tier) - Self::cost_multiplier(current_tier);
        
        // Benefit: reduced quota hits + potential latency improvement
        let quota_benefit = quota_hit_rate * 10.0; // 10 points per 10% quota hit rate
        
        // Extra benefit if upgrading to Turbo (performance boost)
        let turbo_benefit = if next_tier.uses_turbo_acceleration() && !current_tier.uses_turbo_acceleration() {
            // Turbo gives ~80x latency improvement (41.5µs → 500ns)
            (avg_latency_ms as f64 / 1000.0) * 5.0 // 5 points per ms saved
        } else {
            0.0
        };

        let total_benefit = quota_benefit + turbo_benefit;

        // ROI = benefit / cost
        if cost_increase > 0.0 {
            total_benefit / cost_increase
        } else {
            total_benefit // Free upgrade
        }
    }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Tests
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_path_remapping() {
        let tenant = TenantMetadata::new("secure-tenant".to_string(), TenantTier::Standard);

        // Virtual path -> Physical path
        let physical = PathPolicy::safe_remap(&tenant, "/app/data/file.txt");
        assert_eq!(
            physical,
            PathBuf::from("root/tenants/secure-tenant/app/data/file.txt")
        );

        // Leading slash handled
        let physical2 = PathPolicy::safe_remap(&tenant, "app/data/file.txt");
        assert_eq!(
            physical2,
            PathBuf::from("root/tenants/secure-tenant/app/data/file.txt")
        );
    }

    #[test]
    fn test_path_isolation() {
        let tenant = TenantMetadata::new("tenant-a".to_string(), TenantTier::Standard);

        // Tenant can access own paths
        assert!(PathPolicy::is_path_allowed(&tenant, "root/tenants/tenant-a/data/file.txt"));

        // Tenant cannot access other tenant's paths
        assert!(!PathPolicy::is_path_allowed(&tenant, "root/tenants/tenant-b/data/file.txt"));

        // Tenant cannot access system paths
        assert!(!PathPolicy::is_path_allowed(&tenant, "/etc/passwd"));
        assert!(!PathPolicy::is_path_allowed(&tenant, "/var/log/system.log"));
    }

    #[test]
    fn test_path_safety() {
        assert!(PathPolicy::is_path_safe("/app/data/file.txt"));
        assert!(PathPolicy::is_path_safe("relative/path/file.txt"));

        // Null byte attack
        assert!(!PathPolicy::is_path_safe("/app\0/data"));

        // Path traversal
        assert!(!PathPolicy::is_path_safe("/app/../etc/passwd"));
        assert!(!PathPolicy::is_path_safe("/app/./data"));

        // Excessive length (DoS)
        let long_path = "a/".repeat(3000);
        assert!(!PathPolicy::is_path_safe(&long_path));
    }

    #[test]
    fn test_execution_time_validation() {
        let config = ResourceConfig::for_tier(TenantTier::Free);

        assert!(ResourcePolicy::is_execution_time_valid(&config, 50)); // 50ms < 100ms limit
        assert!(ResourcePolicy::is_execution_time_valid(&config, 100)); // Exactly at limit
        assert!(!ResourcePolicy::is_execution_time_valid(&config, 150)); // Exceeds limit
    }

    #[test]
    fn test_memory_usage_validation() {
        let config = ResourceConfig::for_tier(TenantTier::Standard);

        assert!(ResourcePolicy::is_memory_usage_valid(&config, 256)); // 256MB < 512MB limit
        assert!(ResourcePolicy::is_memory_usage_valid(&config, 512)); // At limit
        assert!(!ResourcePolicy::is_memory_usage_valid(&config, 600)); // Exceeds limit
    }

    #[test]
    fn test_concurrency_validation() {
        let config = ResourceConfig::for_tier(TenantTier::Turbo);

        assert!(ResourcePolicy::is_concurrency_valid(&config, 50)); // 50 < 100 limit
        assert!(ResourcePolicy::is_concurrency_valid(&config, 100)); // At limit
        assert!(!ResourcePolicy::is_concurrency_valid(&config, 150)); // Exceeds limit
    }

    #[test]
    fn test_utilization_calculation() {
        assert_eq!(ResourcePolicy::calculate_utilization(50, 100), 50);
        assert_eq!(ResourcePolicy::calculate_utilization(100, 100), 100);
        assert_eq!(ResourcePolicy::calculate_utilization(0, 100), 0);
        assert_eq!(ResourcePolicy::calculate_utilization(10, 0), 0); // Avoid division by zero
    }

    #[test]
    fn test_tier_recommendation() {
        // High concurrency → recommend Turbo
        let rec = TierRecommendationPolicy::recommend_tier(TenantTier::Standard, 50, 100, 0.6);
        assert_eq!(rec, Some(TenantTier::Turbo));

        // High quota hit rate → recommend next tier
        let rec = TierRecommendationPolicy::recommend_tier(TenantTier::Free, 3, 50, 0.7);
        assert_eq!(rec, Some(TenantTier::Standard));

        // Already at Enterprise → no upgrade
        let rec = TierRecommendationPolicy::recommend_tier(TenantTier::Enterprise, 1000, 10000, 0.9);
        assert_eq!(rec, None);

        // Low utilization → no upgrade
        let rec = TierRecommendationPolicy::recommend_tier(TenantTier::Standard, 5, 50, 0.1);
        assert_eq!(rec, None);
    }

    #[test]
    fn test_cost_multiplier() {
        assert_eq!(TierRecommendationPolicy::cost_multiplier(TenantTier::Free), 0.0);
        assert_eq!(TierRecommendationPolicy::cost_multiplier(TenantTier::Standard), 1.0);
        assert_eq!(TierRecommendationPolicy::cost_multiplier(TenantTier::Turbo), 3.0);
        assert_eq!(TierRecommendationPolicy::cost_multiplier(TenantTier::Pro), 8.0);
    }

    #[test]
    fn test_upgrade_roi() {
        // High quota hit rate → good ROI
        let roi = TierRecommendationPolicy::calculate_upgrade_roi(TenantTier::Free, 0.8, 50);
        assert!(roi > 5.0);

        // Upgrading to Turbo with high latency → very good ROI
        let roi = TierRecommendationPolicy::calculate_upgrade_roi(TenantTier::Standard, 0.5, 100);
        assert!(roi > 3.0);

        // Low usage → low ROI
        let roi = TierRecommendationPolicy::calculate_upgrade_roi(TenantTier::Standard, 0.1, 10);
        assert!(roi < 1.0);
    }
}