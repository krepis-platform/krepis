//! Domain Model: Tenant Tier Classification
//! 
//! Pure business logic for tenant subscription tiers and their capabilities.
//! This is the single source of truth for tier hierarchy and feature access.

use serde::{Deserialize, Serialize};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Tenant Tier Enum
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/// Tenant subscription tier
/// 
/// # Tier Progression
/// 
/// ```text
/// Free → Standard → Turbo → Pro → Enterprise
///   ↑       ↑         ↑      ↑        ↑
///  Eval   Basic    Optimized Premium  Custom
/// ```
/// 
/// # Turbo Acceleration Threshold
/// 
/// Only Turbo and above tiers receive zero-copy shared memory optimization.
/// This is enforced by `uses_turbo_acceleration()` method.
/// 
/// # Spec Compliance
/// 
/// - Sovereign-002: Tenant tier determines resource allocation
/// - Sovereign-003: Tier-based concurrency and memory limits
/// - Performance: Turbo+ gets <500ns context sync vs ~41.5µs for Standard FFI
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize, PartialOrd)]
#[repr(u8)]
pub enum TenantTier {
    /// Free tier: Evaluation and hobbyist use
    /// 
    /// - Standard FFI execution only
    /// - 5 concurrent requests max
    /// - 100ms execution timeout
    /// - 128MB memory limit
    Free = 0,

    /// Standard tier: Small business and professional use
    /// 
    /// - Standard FFI execution
    /// - 20 concurrent requests
    /// - 500ms execution timeout
    /// - 512MB memory limit
    Standard = 1,

    /// Turbo tier: Performance-focused customers
    /// 
    /// - **⚡ Zero-copy shared memory acceleration**
    /// - 100 concurrent requests
    /// - 2s execution timeout
    /// - 2GB memory limit
    /// - Sub-microsecond context synchronization
    Turbo = 2,

    /// Pro tier: Power users and growing teams
    /// 
    /// - **⚡ Zero-copy acceleration**
    /// - 500 concurrent requests
    /// - 10s execution timeout
    /// - 8GB memory limit
    /// - Advanced features
    Pro = 3,

    /// Enterprise tier: Mission-critical deployments
    /// 
    /// - **⚡ Zero-copy acceleration**
    /// - Unlimited concurrency (soft limit)
    /// - 60s execution timeout
    /// - Unlimited memory (soft limit)
    /// - **🛡️ Sentinel AI monitoring**
    /// - Custom SLA
    Enterprise = 4,
}

impl TenantTier {
    /// Check if this tier qualifies for Turbo acceleration
    /// 
    /// # Business Rule
    /// 
    /// Only Turbo and above tiers get access to shared memory zero-copy optimization.
    /// This is a key differentiator in the pricing model.
    /// 
    /// # Performance Impact
    /// 
    /// - `false`: Context sync via Protobuf FFI (~41.5µs)
    /// - `true`: Context sync via shared memory (<500ns)
    /// 
    /// # Returns
    /// 
    /// `true` if this tier has Turbo acceleration enabled
    #[inline]
    pub const fn uses_turbo_acceleration(self) -> bool {
        matches!(self, Self::Turbo | Self::Pro | Self::Enterprise)
    }

    /// Check if this tier has Sentinel AI monitoring
    /// 
    /// # Business Rule
    /// 
    /// Only Enterprise tier gets advanced AI-powered anomaly detection.
    /// 
    /// # Returns
    /// 
    /// `true` if Sentinel monitoring is available
    #[inline]
    pub const fn has_sentinel_monitoring(self) -> bool {
        matches!(self, Self::Enterprise)
    }

    /// Get human-readable tier name
    /// 
    /// # Returns
    /// 
    /// Static string slice with tier name
    #[inline]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Free => "Free",
            Self::Standard => "Standard",
            Self::Turbo => "Turbo",
            Self::Pro => "Pro",
            Self::Enterprise => "Enterprise",
        }
    }

    /// Parse tier from numeric value
    /// 
    /// # Arguments
    /// 
    /// * `value` - Numeric tier value (0-4)
    /// 
    /// # Returns
    /// 
    /// `Some(TenantTier)` if valid, `None` if out of range
    pub fn from_u8(value: u8) -> Option<Self> {
        match value {
            0 => Some(Self::Free),
            1 => Some(Self::Standard),
            2 => Some(Self::Turbo),
            3 => Some(Self::Pro),
            4 => Some(Self::Enterprise),
            _ => None,
        }
    }

    /// Get numeric tier value
    /// 
    /// # Returns
    /// 
    /// Tier as u8 (0-4)
    #[inline]
    pub const fn as_u8(self) -> u8 {
        self as u8
    }

    /// Check if upgrade is valid
    /// 
    /// # Business Rule
    /// 
    /// Tiers can only be upgraded (increased), never downgraded.
    /// Downgrades require manual intervention for billing reasons.
    /// 
    /// # Arguments
    /// 
    /// * `target` - Target tier to upgrade to
    /// 
    /// # Returns
    /// 
    /// `true` if upgrade is valid (target > current)
    pub fn can_upgrade_to(self, target: Self) -> bool {
        target.as_u8() > self.as_u8()
    }

    /// Get next tier in progression
    /// 
    /// # Returns
    /// 
    /// Next tier, or `None` if already at Enterprise
    pub fn next_tier(self) -> Option<Self> {
        Self::from_u8(self.as_u8() + 1)
    }

    /// Get previous tier (for reference only)
    /// 
    /// # Returns
    /// 
    /// Previous tier, or `None` if already at Free
    pub fn previous_tier(self) -> Option<Self> {
        if self.as_u8() == 0 {
            None
        } else {
            Self::from_u8(self.as_u8() - 1)
        }
    }
}

impl Default for TenantTier {
    fn default() -> Self {
        Self::Free
    }
}

impl std::fmt::Display for TenantTier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name())
    }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Tests
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tier_hierarchy() {
        assert_eq!(TenantTier::Free.as_u8(), 0);
        assert_eq!(TenantTier::Standard.as_u8(), 1);
        assert_eq!(TenantTier::Turbo.as_u8(), 2);
        assert_eq!(TenantTier::Pro.as_u8(), 3);
        assert_eq!(TenantTier::Enterprise.as_u8(), 4);
    }

    #[test]
    fn test_turbo_acceleration_flag() {
        // Free and Standard: No Turbo
        assert!(!TenantTier::Free.uses_turbo_acceleration());
        assert!(!TenantTier::Standard.uses_turbo_acceleration());

        // Turbo and above: Yes Turbo
        assert!(TenantTier::Turbo.uses_turbo_acceleration());
        assert!(TenantTier::Pro.uses_turbo_acceleration());
        assert!(TenantTier::Enterprise.uses_turbo_acceleration());
    }

    #[test]
    fn test_sentinel_monitoring_flag() {
        assert!(!TenantTier::Free.has_sentinel_monitoring());
        assert!(!TenantTier::Standard.has_sentinel_monitoring());
        assert!(!TenantTier::Turbo.has_sentinel_monitoring());
        assert!(!TenantTier::Pro.has_sentinel_monitoring());
        assert!(TenantTier::Enterprise.has_sentinel_monitoring());
    }

    #[test]
    fn test_tier_parsing() {
        assert_eq!(TenantTier::from_u8(0), Some(TenantTier::Free));
        assert_eq!(TenantTier::from_u8(2), Some(TenantTier::Turbo));
        assert_eq!(TenantTier::from_u8(4), Some(TenantTier::Enterprise));
        assert_eq!(TenantTier::from_u8(5), None);
        assert_eq!(TenantTier::from_u8(255), None);
    }

    #[test]
    fn test_tier_names() {
        assert_eq!(TenantTier::Free.name(), "Free");
        assert_eq!(TenantTier::Turbo.name(), "Turbo");
        assert_eq!(format!("{}", TenantTier::Enterprise), "Enterprise");
    }

    #[test]
    fn test_upgrade_validation() {
        let free = TenantTier::Free;
        let standard = TenantTier::Standard;
        let turbo = TenantTier::Turbo;

        // Valid upgrades
        assert!(free.can_upgrade_to(standard));
        assert!(free.can_upgrade_to(turbo));
        assert!(standard.can_upgrade_to(TenantTier::Enterprise));

        // Invalid upgrades (downgrades)
        assert!(!turbo.can_upgrade_to(standard));
        assert!(!standard.can_upgrade_to(free));

        // Same tier (not an upgrade)
        assert!(!turbo.can_upgrade_to(turbo));
    }

    #[test]
    fn test_tier_progression() {
        assert_eq!(TenantTier::Free.next_tier(), Some(TenantTier::Standard));
        assert_eq!(TenantTier::Standard.next_tier(), Some(TenantTier::Turbo));
        assert_eq!(TenantTier::Turbo.next_tier(), Some(TenantTier::Pro));
        assert_eq!(TenantTier::Pro.next_tier(), Some(TenantTier::Enterprise));
        assert_eq!(TenantTier::Enterprise.next_tier(), None);

        assert_eq!(TenantTier::Free.previous_tier(), None);
        assert_eq!(TenantTier::Standard.previous_tier(), Some(TenantTier::Free));
        assert_eq!(TenantTier::Enterprise.previous_tier(), Some(TenantTier::Pro));
    }

    #[test]
    fn test_default_tier() {
        assert_eq!(TenantTier::default(), TenantTier::Free);
    }

    #[test]
    fn test_serialization() {
        use serde_json;

        let tier = TenantTier::Turbo;
        let json = serde_json::to_string(&tier).unwrap();
        assert!(json.contains("2")); // Turbo = 2

        let deserialized: TenantTier = serde_json::from_str(&json).unwrap();
        assert_eq!(deserialized, TenantTier::Turbo);
    }
}