//! Domain Module: Tenant Management
//! 
//! Pure business logic for tenant identity, tiers, resource policies, and validation.
//! This module is completely independent of infrastructure concerns.
//! 
//! # Architecture
//! 
//! This module follows the Domain-Driven Design pattern where:
//! - **Entities**: `TenantMetadata` - Core domain objects with identity
//! - **Value Objects**: `TenantTier`, `ResourceConfig` - Immutable data
//! - **Policies**: `PathPolicy`, `ResourcePolicy`, `TierRecommendationPolicy` - Business rules
//! - **Errors**: `TenantError` - Domain-level error types
//! 
//! # Spec Compliance
//! 
//! - **Sovereign-002**: Tenant context identification and resource mapping
//! - **Sovereign-003**: Resource quota and performance guardrails
//! - **Spec-008**: Error code mapping for SDK propagation
//! 
//! # Zero-Copy Readiness
//! 
//! This module is designed to support both:
//! - **Standard FFI**: Protobuf serialization (~41.5µs context sync)
//! - **Turbo Acceleration**: Shared memory zero-copy (<500ns context sync)
//! 
//! The decision is made at domain level via `TenantTier::uses_turbo_acceleration()`,
//! and implemented at adapters level.

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Module Declarations
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

pub mod tier;
pub mod model;
pub mod error;
pub mod policy;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Public Re-exports (Flattened API)
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// Core types
pub use tier::TenantTier;
pub use model::{TenantMetadata, ResourceConfig};
pub use error::TenantError;

// Policy functions
pub use policy::{
    PathPolicy,
    ResourcePolicy,
    TierRecommendationPolicy,
};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Module Documentation Examples
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/// # Example: Creating a Tenant
/// 
/// ```rust
/// use krepis_kernel::domain::tenant::{TenantMetadata, TenantTier};
/// 
/// let tenant = TenantMetadata::new("acme-corp".to_string(), TenantTier::Turbo);
/// 
/// assert_eq!(tenant.tier(), TenantTier::Turbo);
/// assert!(tenant.uses_turbo()); // Zero-copy acceleration enabled
/// assert_eq!(tenant.storage_tree, "tenant_db_acme-corp");
/// ```
/// 
/// # Example: Checking Resource Limits
/// 
/// ```rust
/// use krepis_kernel::domain::tenant::{TenantMetadata, TenantTier, ResourcePolicy};
/// 
/// let tenant = TenantMetadata::new("startup".to_string(), TenantTier::Free);
/// let config = tenant.resource_config();
/// 
/// // Check if execution time is valid
/// assert!(ResourcePolicy::is_execution_time_valid(config, 50)); // 50ms OK
/// assert!(!ResourcePolicy::is_execution_time_valid(config, 200)); // 200ms exceeds 100ms limit
/// ```
/// 
/// # Example: Path Security
/// 
/// ```rust
/// use krepis_kernel::domain::tenant::{TenantMetadata, TenantTier, PathPolicy};
/// 
/// let tenant = TenantMetadata::new("secure-app".to_string(), TenantTier::Standard);
/// 
/// // Virtual path -> Physical path
/// let physical = PathPolicy::safe_remap(&tenant, "/app/data/file.txt");
/// assert_eq!(physical.to_str().unwrap(), "root/tenants/secure-app/app/data/file.txt");
/// 
/// // Tenant isolation check
/// assert!(PathPolicy::is_path_allowed(&tenant, "root/tenants/secure-app/data/file.txt"));
/// assert!(!PathPolicy::is_path_allowed(&tenant, "root/tenants/other-app/data/file.txt"));
/// ```
/// 
/// # Example: Tier Upgrade
/// 
/// ```rust
/// use krepis_kernel::domain::tenant::{TenantMetadata, TenantTier};
/// 
/// let mut tenant = TenantMetadata::new("growing-startup".to_string(), TenantTier::Free);
/// 
/// // Upgrade to Turbo for performance
/// tenant.upgrade_tier(TenantTier::Turbo).unwrap();
/// 
/// assert_eq!(tenant.tier(), TenantTier::Turbo);
/// assert!(tenant.uses_turbo()); // Now gets zero-copy acceleration
/// assert_eq!(tenant.resource_config().max_concurrent_requests, 100);
/// ```
/// 
/// # Example: Tier Recommendation
/// 
/// ```rust
/// use krepis_kernel::domain::tenant::{TenantTier, TierRecommendationPolicy};
/// 
/// // Analyze usage pattern
/// let current_tier = TenantTier::Standard;
/// let avg_concurrent = 50; // High concurrency
/// let avg_exec_time_ms = 100;
/// let quota_hit_rate = 0.7; // Hitting quota 70% of the time
/// 
/// let recommendation = TierRecommendationPolicy::recommend_tier(
///     current_tier,
///     avg_concurrent,
///     avg_exec_time_ms,
///     quota_hit_rate,
/// );
/// 
/// assert_eq!(recommendation, Some(TenantTier::Turbo)); // Recommend Turbo for performance
/// ```
/// 
/// # Example: Error Handling
/// 
/// ```rust
/// use krepis_kernel::domain::tenant::{TenantMetadata, TenantTier, TenantError};
/// 
/// let mut tenant = TenantMetadata::new("test".to_string(), TenantTier::Turbo);
/// 
/// // Try invalid downgrade
/// let result = tenant.upgrade_tier(TenantTier::Standard);
/// 
/// match result {
///     Err(TenantError::InvalidTierChange { current, requested }) => {
///         assert_eq!(current, TenantTier::Turbo);
///         assert_eq!(requested, TenantTier::Standard);
///     }
///     _ => panic!("Expected InvalidTierChange error"),
/// }
/// ```
/// 
/// # Example: Turbo Error Handling
/// 
/// ```rust
/// use krepis_kernel::domain::tenant::{TenantTier, TenantError};
/// 
/// let error = TenantError::TurboPoolExhausted {
///     tenant_id: "high-load-app".to_string(),
///     available: 0,
///     required: 5,
/// };
/// 
/// assert!(error.is_turbo_error());
/// assert!(error.is_recoverable());
/// assert_eq!(error.to_proto_code(), 3001);
/// assert_eq!(error.to_proto_category(), "TURBO_ERROR");
/// ```
#[cfg(doc)]
pub mod examples {}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Integration Tests
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

#[cfg(test)]
mod integration_tests {
    use super::*;

    #[test]
    fn test_tenant_lifecycle() {
        // Create tenant
        let mut tenant = TenantMetadata::new("lifecycle-test".to_string(), TenantTier::Free);

        // Validate initial state
        assert_eq!(tenant.tier(), TenantTier::Free);
        assert!(!tenant.uses_turbo());
        assert!(tenant.validate().is_ok());

        // Upgrade to Turbo
        tenant.upgrade_tier(TenantTier::Turbo).unwrap();
        assert!(tenant.uses_turbo());

        // Cannot downgrade
        assert!(tenant.upgrade_tier(TenantTier::Standard).is_err());

        // Deactivate tenant
        tenant.active = false;
        assert!(tenant.validate().is_err());
    }

    #[test]
    fn test_cross_tier_policies() {
        // Test that policies work consistently across all tiers
        for tier_value in 0..=4 {
            let tier = TenantTier::from_u8(tier_value).unwrap();
            let tenant = TenantMetadata::new(format!("tier-{}", tier_value), tier);
            let config = tenant.resource_config();

            // All tiers should have valid configurations
            assert!(config.max_concurrent_requests > 0);
            assert!(config.max_execution_time.as_millis() > 0);
            assert!(config.max_memory_mb > 0);

            // Turbo flag should match tier capability
            assert_eq!(config.use_turbo_acceleration, tier.uses_turbo_acceleration());

            // Path policies should work for all tiers
            let physical = PathPolicy::safe_remap(&tenant, "/app/test");
            assert!(PathPolicy::is_path_allowed(&tenant, &physical));
        }
    }

    #[test]
    fn test_turbo_tier_consistency() {
        // Turbo, Pro, and Enterprise should all have Turbo enabled
        for tier in [TenantTier::Turbo, TenantTier::Pro, TenantTier::Enterprise] {
            let tenant = TenantMetadata::new("turbo-test".to_string(), tier);
            
            assert!(tenant.uses_turbo());
            assert!(tenant.resource_config().use_turbo_acceleration);
            assert_eq!(tier.uses_turbo_acceleration(), true);
        }

        // Free and Standard should not have Turbo
        for tier in [TenantTier::Free, TenantTier::Standard] {
            let tenant = TenantMetadata::new("standard-test".to_string(), tier);
            
            assert!(!tenant.uses_turbo());
            assert!(!tenant.resource_config().use_turbo_acceleration);
            assert_eq!(tier.uses_turbo_acceleration(), false);
        }
    }

    #[test]
    fn test_error_code_consistency() {
        // Test that all errors have valid codes and categories
        let errors = vec![
            TenantError::NotFound("x".into()),
            TenantError::Inactive("x".into()),
            TenantError::QuotaExceeded("x".into()),
            TenantError::ExecutionTimeout {
                tenant_id: "x".into(),
                limit_ms: 100,
                elapsed_ms: 150,
            },
            TenantError::TurboPoolExhausted {
                tenant_id: "x".into(),
                available: 0,
                required: 1,
            },
            TenantError::TurboNotAvailable {
                tenant_id: "x".into(),
                tier: TenantTier::Free,
            },
        ];

        for error in errors {
            let code = error.to_proto_code();
            let category = error.to_proto_category();

            // Code should be in valid range
            assert!(code >= 1000 && code <= 9999);

            // Category should not be empty
            assert!(!category.is_empty());

            // Error message should not be empty
            assert!(!error.to_string().is_empty());
        }
    }

    #[test]
    fn test_recommendation_engine() {
        // Test recommendation engine with realistic scenarios

        // Scenario 1: Startup hitting Free tier limits
        let rec = TierRecommendationPolicy::recommend_tier(TenantTier::Free, 4, 90, 0.8);
        assert_eq!(rec, Some(TenantTier::Standard));

        // Scenario 2: Growing company needs performance
        let rec = TierRecommendationPolicy::recommend_tier(TenantTier::Standard, 40, 200, 0.6);
        assert_eq!(rec, Some(TenantTier::Turbo));

        // Scenario 3: Power user needs extended limits
        let rec = TierRecommendationPolicy::recommend_tier(TenantTier::Turbo, 200, 1500, 0.5);
        assert_eq!(rec, Some(TenantTier::Pro));

        // Scenario 4: Already at max tier
        let rec = TierRecommendationPolicy::recommend_tier(TenantTier::Enterprise, 1000, 10000, 0.9);
        assert_eq!(rec, None);
    }
}