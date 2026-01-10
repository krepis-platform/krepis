//! Domain Model: Pool Policy
//! 
//! Pure business logic for resource pooling, eviction, storage routing, and preemption.
//! No infrastructure concerns - these are decision rules for adapters to implement.

use std::time::{Duration, Instant};

use crate::domain::tenant::TenantTier;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Storage Strategy
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/// Storage strategy for tenant execution context
/// 
/// This is a domain-level decision that the adapters layer implements.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StorageStrategy {
    /// Standard FFI-based storage
    /// 
    /// - Uses Protobuf serialization
    /// - ~41.5µs context synchronization
    /// - Used by Free and Standard tiers
    Standard,

    /// Zero-copy shared memory storage
    /// 
    /// - Direct memory access
    /// - <500ns context synchronization
    /// - Used by Turbo, Pro, and Enterprise tiers
    Turbo,
}

impl StorageStrategy {
    /// Get expected synchronization latency in nanoseconds
    /// 
    /// These are target values for monitoring and alerting.
    /// 
    /// # Returns
    /// 
    /// Expected latency in nanoseconds
    pub fn expected_latency_ns(self) -> u64 {
        match self {
            Self::Standard => 41_500, // 41.5µs
            Self::Turbo => 500,       // 500ns
        }
    }

    /// Check if this strategy uses zero-copy optimization
    /// 
    /// # Returns
    /// 
    /// `true` if zero-copy is enabled
    pub fn is_zero_copy(self) -> bool {
        matches!(self, Self::Turbo)
    }

    /// Get human-readable name
    /// 
    /// # Returns
    /// 
    /// Strategy name
    pub fn name(self) -> &'static str {
        match self {
            Self::Standard => "Standard-FFI",
            Self::Turbo => "Turbo-ZeroCopy",
        }
    }
}

impl std::fmt::Display for StorageStrategy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name())
    }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Pool Policy (Pure Strategy Functions)
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/// Pool management policies
/// 
/// These are pure functions that make decisions based on domain rules.
/// The adapters layer implements these decisions.
pub struct PoolPolicy;

impl PoolPolicy {
    /// Determine if an idle resource should be evicted
    /// 
    /// # Business Rule
    /// 
    /// Evict resources that have been idle longer than the configured max_idle_time.
    /// This prevents memory bloat while maintaining warm cache for active tenants.
    /// 
    /// # Arguments
    /// 
    /// * `last_used` - When the resource was last accessed
    /// * `max_idle` - Maximum allowed idle time
    /// 
    /// # Returns
    /// 
    /// `true` if resource should be evicted
    pub fn should_evict(last_used: Instant, max_idle: Duration) -> bool {
        last_used.elapsed() > max_idle
    }

    /// Determine storage strategy for a tenant tier
    /// 
    /// # Business Rule
    /// 
    /// - Free/Standard: Use Standard FFI-based storage (~41.5µs)
    /// - Turbo+: Use Zero-copy shared memory storage (<500ns)
    /// 
    /// This is the domain's declaration of "which tier gets which performance level."
    /// The adapters layer (ContextPool) implements this by routing to the appropriate
    /// storage backend.
    /// 
    /// # Arguments
    /// 
    /// * `tier` - Tenant tier
    /// 
    /// # Returns
    /// 
    /// * `StorageStrategy::Standard` - Use Protobuf FFI
    /// * `StorageStrategy::Turbo` - Use shared memory
    pub fn determine_storage_strategy(tier: TenantTier) -> StorageStrategy {
        if tier.uses_turbo_acceleration() {
            StorageStrategy::Turbo
        } else {
            StorageStrategy::Standard
        }
    }

    /// Calculate priority for resource allocation
    /// 
    /// # Business Rule
    /// 
    /// Higher tiers get priority when resources are scarce.
    /// This ensures paying customers have better experience during congestion.
    /// 
    /// # Priority Scale
    /// 
    /// - Free: 1 (lowest)
    /// - Standard: 2
    /// - Turbo: 5
    /// - Pro: 8
    /// - Enterprise: 10 (highest)
    /// 
    /// # Arguments
    /// 
    /// * `tier` - Tenant tier
    /// 
    /// # Returns
    /// 
    /// Priority value (higher = more important)
    pub fn allocation_priority(tier: TenantTier) -> u8 {
        match tier {
            TenantTier::Free => 1,
            TenantTier::Standard => 2,
            TenantTier::Turbo => 5,
            TenantTier::Pro => 8,
            TenantTier::Enterprise => 10,
        }
    }

    /// Determine if a tenant can preempt another tenant's resources
    /// 
    /// # Business Rule (Preemption Matrix)
    /// 
    /// When resources are scarce, higher tiers can forcibly evict lower tiers:
    /// 
    /// | Requester     | Can Preempt          |
    /// |---------------|----------------------|
    /// | Free          | None                 |
    /// | Standard      | Free                 |
    /// | Turbo         | Free, Standard       |
    /// | Pro           | Free, Standard       |
    /// | Enterprise    | All lower tiers      |
    /// 
    /// # Arguments
    /// 
    /// * `requester` - Tier requesting resources
    /// * `victim` - Tier currently holding resources
    /// 
    /// # Returns
    /// 
    /// `true` if requester can preempt victim
    /// 
    /// # Example
    /// 
    /// ```
    /// use krepis_kernel::domain::{TenantTier, PoolPolicy};
    /// 
    /// // Enterprise can preempt Free
    /// assert!(PoolPolicy::can_preempt(TenantTier::Enterprise, TenantTier::Free));
    /// 
    /// // Free cannot preempt Standard
    /// assert!(!PoolPolicy::can_preempt(TenantTier::Free, TenantTier::Standard));
    /// 
    /// // Same tier cannot preempt each other
    /// assert!(!PoolPolicy::can_preempt(TenantTier::Turbo, TenantTier::Turbo));
    /// ```
    pub fn can_preempt(requester: TenantTier, victim: TenantTier) -> bool {
        let requester_priority = Self::allocation_priority(requester);
        let victim_priority = Self::allocation_priority(victim);

        // Can only preempt strictly lower priority tiers
        requester_priority > victim_priority
    }

    /// Find best victim for preemption
    /// 
    /// # Business Rule
    /// 
    /// When multiple victims are available, choose the one with:
    /// 1. Lowest priority (tier)
    /// 2. Longest idle time (among same priority)
    /// 
    /// # Arguments
    /// 
    /// * `requester` - Tier requesting resources
    /// * `candidates` - List of (tier, last_used) tuples
    /// 
    /// # Returns
    /// 
    /// Index of best victim, or `None` if no valid victim
    pub fn select_preemption_victim(
        requester: TenantTier,
        candidates: &[(TenantTier, Instant)],
    ) -> Option<usize> {
        let mut best_victim: Option<(usize, u8, Duration)> = None;

        for (idx, (victim_tier, last_used)) in candidates.iter().enumerate() {
            // Can we preempt this tier?
            if !Self::can_preempt(requester, *victim_tier) {
                continue;
            }

            let priority = Self::allocation_priority(*victim_tier);
            let idle_time = last_used.elapsed();

            match best_victim {
                None => {
                    // First valid victim
                    best_victim = Some((idx, priority, idle_time));
                }
                Some((_, best_priority, best_idle)) => {
                    // Prefer lower priority, or longer idle time if same priority
                    if priority < best_priority || (priority == best_priority && idle_time > best_idle) {
                        best_victim = Some((idx, priority, idle_time));
                    }
                }
            }
        }

        best_victim.map(|(idx, _, _)| idx)
    }

    /// Determine if a tenant should be throttled
    /// 
    /// # Business Rule
    /// 
    /// Free tier has aggressive rate limiting to prevent abuse.
    /// Paid tiers have generous limits.
    /// 
    /// # Arguments
    /// 
    /// * `tier` - Tenant tier
    /// * `requests_per_minute` - Current request rate
    /// 
    /// # Returns
    /// 
    /// `true` if tenant should be throttled
    pub fn should_throttle(tier: TenantTier, requests_per_minute: u64) -> bool {
        let limit = match tier {
            TenantTier::Free => 60,       // 1 req/sec
            TenantTier::Standard => 300,  // 5 req/sec
            TenantTier::Turbo => 1200,    // 20 req/sec
            TenantTier::Pro => 6000,      // 100 req/sec
            TenantTier::Enterprise => u64::MAX, // Unlimited
        };

        requests_per_minute > limit
    }

    /// Calculate LRU eviction age threshold
    /// 
    /// # Business Rule
    /// 
    /// Keep warm caches for paid tiers longer than free tier.
    /// 
    /// # Arguments
    /// 
    /// * `tier` - Tenant tier
    /// 
    /// # Returns
    /// 
    /// Maximum idle time before eviction
    pub fn eviction_threshold(tier: TenantTier) -> Duration {
        match tier {
            TenantTier::Free => Duration::from_secs(60),        // 1 minute
            TenantTier::Standard => Duration::from_secs(300),   // 5 minutes
            TenantTier::Turbo => Duration::from_secs(600),      // 10 minutes
            TenantTier::Pro => Duration::from_secs(1800),       // 30 minutes
            TenantTier::Enterprise => Duration::from_secs(3600), // 1 hour
        }
    }

    /// Calculate recommended pool size for a tier
    /// 
    /// # Business Rule
    /// 
    /// Higher tiers get more pool capacity to handle burst traffic.
    /// 
    /// # Arguments
    /// 
    /// * `tier` - Tenant tier
    /// 
    /// # Returns
    /// 
    /// Recommended pool size for this tier
    pub fn recommended_pool_size(tier: TenantTier) -> usize {
        match tier {
            TenantTier::Free => 10,
            TenantTier::Standard => 50,
            TenantTier::Turbo => 200,
            TenantTier::Pro => 500,
            TenantTier::Enterprise => 1000,
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
    fn test_should_evict() {
        let now = Instant::now();
        let max_idle = Duration::from_secs(300);

        // Not yet idle
        assert!(!PoolPolicy::should_evict(now, max_idle));

        // Simulate time passing
        let old_time = now - Duration::from_secs(400);
        assert!(PoolPolicy::should_evict(old_time, max_idle));
    }

    #[test]
    fn test_storage_strategy_determination() {
        assert_eq!(
            PoolPolicy::determine_storage_strategy(TenantTier::Free),
            StorageStrategy::Standard
        );
        assert_eq!(
            PoolPolicy::determine_storage_strategy(TenantTier::Standard),
            StorageStrategy::Standard
        );
        assert_eq!(
            PoolPolicy::determine_storage_strategy(TenantTier::Turbo),
            StorageStrategy::Turbo
        );
        assert_eq!(
            PoolPolicy::determine_storage_strategy(TenantTier::Pro),
            StorageStrategy::Turbo
        );
        assert_eq!(
            PoolPolicy::determine_storage_strategy(TenantTier::Enterprise),
            StorageStrategy::Turbo
        );
    }

    #[test]
    fn test_allocation_priority() {
        assert_eq!(PoolPolicy::allocation_priority(TenantTier::Free), 1);
        assert_eq!(PoolPolicy::allocation_priority(TenantTier::Standard), 2);
        assert_eq!(PoolPolicy::allocation_priority(TenantTier::Turbo), 5);
        assert_eq!(PoolPolicy::allocation_priority(TenantTier::Pro), 8);
        assert_eq!(PoolPolicy::allocation_priority(TenantTier::Enterprise), 10);
    }

    #[test]
    fn test_preemption_rules() {
        // Enterprise can preempt everyone
        assert!(PoolPolicy::can_preempt(TenantTier::Enterprise, TenantTier::Free));
        assert!(PoolPolicy::can_preempt(TenantTier::Enterprise, TenantTier::Standard));
        assert!(PoolPolicy::can_preempt(TenantTier::Enterprise, TenantTier::Turbo));
        assert!(PoolPolicy::can_preempt(TenantTier::Enterprise, TenantTier::Pro));

        // Turbo can preempt Free and Standard
        assert!(PoolPolicy::can_preempt(TenantTier::Turbo, TenantTier::Free));
        assert!(PoolPolicy::can_preempt(TenantTier::Turbo, TenantTier::Standard));
        assert!(!PoolPolicy::can_preempt(TenantTier::Turbo, TenantTier::Pro));

        // Free cannot preempt anyone
        assert!(!PoolPolicy::can_preempt(TenantTier::Free, TenantTier::Standard));
        assert!(!PoolPolicy::can_preempt(TenantTier::Free, TenantTier::Turbo));

        // Same tier cannot preempt each other
        assert!(!PoolPolicy::can_preempt(TenantTier::Standard, TenantTier::Standard));
        assert!(!PoolPolicy::can_preempt(TenantTier::Turbo, TenantTier::Turbo));
    }

    #[test]
    fn test_select_preemption_victim() {
        let now = Instant::now();
        let old = now - Duration::from_secs(100);
        let very_old = now - Duration::from_secs(500);

        let candidates = vec![
            (TenantTier::Standard, now),      // Index 0: recent Standard
            (TenantTier::Free, old),          // Index 1: old Free
            (TenantTier::Free, very_old),     // Index 2: very old Free
            (TenantTier::Turbo, old),         // Index 3: old Turbo
        ];

        // Enterprise requesting: should preempt very old Free (index 2)
        let victim = PoolPolicy::select_preemption_victim(TenantTier::Enterprise, &candidates);
        assert_eq!(victim, Some(2)); // Lowest priority + longest idle

        // Turbo requesting: can preempt Free and Standard
        let victim = PoolPolicy::select_preemption_victim(TenantTier::Turbo, &candidates);
        assert_eq!(victim, Some(2)); // Free tier, longest idle

        // Free requesting: cannot preempt anyone
        let victim = PoolPolicy::select_preemption_victim(TenantTier::Free, &candidates);
        assert_eq!(victim, None);
    }

    #[test]
    fn test_throttling() {
        // Free tier should be throttled at 61 req/min
        assert!(PoolPolicy::should_throttle(TenantTier::Free, 61));
        assert!(!PoolPolicy::should_throttle(TenantTier::Free, 59));

        // Turbo tier has higher limit
        assert!(!PoolPolicy::should_throttle(TenantTier::Turbo, 1000));
        assert!(PoolPolicy::should_throttle(TenantTier::Turbo, 1300));

        // Enterprise is unlimited
        assert!(!PoolPolicy::should_throttle(TenantTier::Enterprise, 1_000_000));
    }

    #[test]
    fn test_eviction_thresholds() {
        assert_eq!(
            PoolPolicy::eviction_threshold(TenantTier::Free),
            Duration::from_secs(60)
        );
        assert_eq!(
            PoolPolicy::eviction_threshold(TenantTier::Turbo),
            Duration::from_secs(600)
        );
        assert_eq!(
            PoolPolicy::eviction_threshold(TenantTier::Enterprise),
            Duration::from_secs(3600)
        );
    }

    #[test]
    fn test_recommended_pool_sizes() {
        assert_eq!(PoolPolicy::recommended_pool_size(TenantTier::Free), 10);
        assert_eq!(PoolPolicy::recommended_pool_size(TenantTier::Standard), 50);
        assert_eq!(PoolPolicy::recommended_pool_size(TenantTier::Turbo), 200);
        assert_eq!(PoolPolicy::recommended_pool_size(TenantTier::Pro), 500);
        assert_eq!(PoolPolicy::recommended_pool_size(TenantTier::Enterprise), 1000);
    }

    #[test]
    fn test_storage_strategy_properties() {
        assert_eq!(StorageStrategy::Standard.expected_latency_ns(), 41_500);
        assert_eq!(StorageStrategy::Turbo.expected_latency_ns(), 500);

        assert!(!StorageStrategy::Standard.is_zero_copy());
        assert!(StorageStrategy::Turbo.is_zero_copy());

        assert_eq!(StorageStrategy::Standard.name(), "Standard-FFI");
        assert_eq!(StorageStrategy::Turbo.name(), "Turbo-ZeroCopy");
    }

    #[test]
    fn test_storage_strategy_display() {
        assert_eq!(format!("{}", StorageStrategy::Standard), "Standard-FFI");
        assert_eq!(format!("{}", StorageStrategy::Turbo), "Turbo-ZeroCopy");
    }
}