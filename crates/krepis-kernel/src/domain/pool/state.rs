//! Domain Model: Pool State
//! 
//! Observability and health monitoring for resource pools.

use serde::{Deserialize, Serialize};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Pool Snapshot
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/// Pool state snapshot for monitoring and observability
/// 
/// This provides a complete view of pool utilization, separating
/// Turbo (zero-copy) and Standard (FFI) execution paths.
/// 
/// # Spec Compliance
/// 
/// - Sovereign-001: Isolate pooling metrics
/// - Performance: Turbo vs Standard tracking
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct PoolSnapshot {
    /// Total number of cached isolates (warm pool size)
    /// 
    /// This includes both Turbo and Standard isolates.
    pub cached_isolates: usize,

    /// Maximum pool capacity (total slots available)
    pub max_capacity: usize,

    /// Overall health status
    pub healthy: bool,

    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // Turbo Pool Metrics (Zero-Copy Shared Memory)
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    /// Number of active Turbo (zero-copy) slots currently in use
    /// 
    /// These are tenants with Turbo+ tier actively executing.
    pub turbo_active: usize,

    /// Total Turbo slots allocated in shared memory pool
    /// 
    /// This is the capacity for zero-copy executions.
    pub turbo_capacity: usize,

    /// Turbo pool utilization percentage (0-100)
    /// 
    /// Calculated as: (turbo_active / turbo_capacity) * 100
    pub turbo_utilization_pct: u8,

    /// Number of times Turbo pool was exhausted
    /// 
    /// When Turbo pool is full, new Turbo-tier tenants fall back to Standard FFI.
    /// High fallback count indicates need to scale Turbo pool.
    pub turbo_fallback_count: u64,

    /// Average Turbo slot reuse count
    /// 
    /// How many times each slot has been reused on average.
    /// Higher values indicate good cache utilization.
    pub turbo_avg_reuse_count: u64,

    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // Standard Pool Metrics (Protobuf FFI)
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    /// Number of active Standard (FFI) isolates currently in use
    /// 
    /// These are Free/Standard tier tenants or Turbo-tier fallbacks.
    pub standard_active: usize,

    /// Total Standard isolate capacity
    /// 
    /// This is the V8 isolate pool size for FFI-based execution.
    pub standard_capacity: usize,

    /// Standard pool utilization percentage (0-100)
    /// 
    /// Calculated as: (standard_active / standard_capacity) * 100
    pub standard_utilization_pct: u8,

    /// Average Standard isolate lifetime (seconds)
    /// 
    /// How long isolates stay in pool before eviction.
    pub standard_avg_lifetime_secs: u64,
}

impl PoolSnapshot {
    /// Calculate overall pool utilization percentage
    /// 
    /// # Returns
    /// 
    /// Utilization percentage (0-100)
    pub fn overall_utilization_pct(&self) -> u8 {
        if self.max_capacity == 0 {
            return 0;
        }

        let used = self.cached_isolates;
        let total = self.max_capacity;

        ((used as f64 / total as f64) * 100.0) as u8
    }

    /// Check if pool is under pressure
    /// 
    /// # Business Rule
    /// 
    /// Pool is under pressure if overall utilization exceeds 80%.
    /// 
    /// # Returns
    /// 
    /// `true` if pool is under pressure
    pub fn is_under_pressure(&self) -> bool {
        self.overall_utilization_pct() > 80
    }

    /// Check if Turbo pool needs scaling
    /// 
    /// # Business Rule
    /// 
    /// Turbo pool should be scaled up if:
    /// - Utilization > 90%, OR
    /// - Fallback count is increasing rapidly (>100)
    /// 
    /// # Returns
    /// 
    /// `true` if Turbo pool should be scaled
    pub fn should_scale_turbo(&self) -> bool {
        self.turbo_utilization_pct > 90 || self.turbo_fallback_count > 100
    }

    /// Check if Standard pool needs scaling
    /// 
    /// # Business Rule
    /// 
    /// Standard pool should be scaled if utilization > 85%.
    /// 
    /// # Returns
    /// 
    /// `true` if Standard pool should be scaled
    pub fn should_scale_standard(&self) -> bool {
        self.standard_utilization_pct > 85
    }

    /// Get Turbo adoption rate
    /// 
    /// # Business Metric
    /// 
    /// What percentage of active executions are using Turbo?
    /// This helps track tier adoption and revenue potential.
    /// 
    /// # Returns
    /// 
    /// Adoption rate (0.0-100.0)
    pub fn turbo_adoption_rate(&self) -> f64 {
        let total_active = self.turbo_active + self.standard_active;
        if total_active == 0 {
            return 0.0;
        }

        (self.turbo_active as f64 / total_active as f64) * 100.0
    }

    /// Get Turbo pool efficiency score
    /// 
    /// # Business Metric
    /// 
    /// Efficiency = (reuse_count * utilization) / 100
    /// 
    /// Higher scores indicate better ROI on Turbo infrastructure.
    /// 
    /// # Returns
    /// 
    /// Efficiency score (0.0-infinity)
    pub fn turbo_efficiency_score(&self) -> f64 {
        let utilization = self.turbo_utilization_pct as f64 / 100.0;
        self.turbo_avg_reuse_count as f64 * utilization
    }

    /// Get available Turbo slots
    /// 
    /// # Returns
    /// 
    /// Number of free Turbo slots
    pub fn turbo_available(&self) -> usize {
        self.turbo_capacity.saturating_sub(self.turbo_active)
    }

    /// Get available Standard slots
    /// 
    /// # Returns
    /// 
    /// Number of free Standard slots
    pub fn standard_available(&self) -> usize {
        self.standard_capacity.saturating_sub(self.standard_active)
    }

    /// Check if Turbo pool has capacity
    /// 
    /// # Returns
    /// 
    /// `true` if at least one Turbo slot is available
    pub fn has_turbo_capacity(&self) -> bool {
        self.turbo_available() > 0
    }

    /// Check if Standard pool has capacity
    /// 
    /// # Returns
    /// 
    /// `true` if at least one Standard slot is available
    pub fn has_standard_capacity(&self) -> bool {
        self.standard_available() > 0
    }
}

impl Default for PoolSnapshot {
    fn default() -> Self {
        Self {
            cached_isolates: 0,
            max_capacity: 0,
            healthy: true,
            turbo_active: 0,
            turbo_capacity: 0,
            turbo_utilization_pct: 0,
            turbo_fallback_count: 0,
            turbo_avg_reuse_count: 0,
            standard_active: 0,
            standard_capacity: 0,
            standard_utilization_pct: 0,
            standard_avg_lifetime_secs: 0,
        }
    }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Health Status
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/// Pool health assessment
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum HealthStatus {
    /// All systems operating normally
    Healthy,

    /// Operating but under stress
    Degraded { reason: String },

    /// Critical issues detected
    Unhealthy { reason: String },
}

impl HealthStatus {
    /// Check if status is healthy
    pub fn is_healthy(&self) -> bool {
        matches!(self, Self::Healthy)
    }

    /// Check if status is degraded
    pub fn is_degraded(&self) -> bool {
        matches!(self, Self::Degraded { .. })
    }

    /// Check if status is unhealthy
    pub fn is_unhealthy(&self) -> bool {
        matches!(self, Self::Unhealthy { .. })
    }

    /// Get reason if not healthy
    pub fn reason(&self) -> Option<&str> {
        match self {
            Self::Healthy => None,
            Self::Degraded { reason } | Self::Unhealthy { reason } => Some(reason),
        }
    }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Health Check
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/// Pool health assessment logic
pub struct PoolHealthCheck;

impl PoolHealthCheck {
    /// Assess pool health based on snapshot
    /// 
    /// # Business Rules
    /// 
    /// - **Unhealthy**: Overall utilization >= 95%
    /// - **Degraded**: Turbo utilization > 85% OR high fallback rate
    /// - **Healthy**: All metrics within normal ranges
    /// 
    /// # Arguments
    /// 
    /// * `snapshot` - Current pool state
    /// 
    /// # Returns
    /// 
    /// Health status with reason if not healthy
    pub fn assess(snapshot: &PoolSnapshot) -> HealthStatus {
        // Critical: Pool near capacity
        if snapshot.overall_utilization_pct() >= 95 {
            return HealthStatus::Unhealthy {
                reason: "Pool near capacity".to_string(),
            };
        }

        // Critical: Both pools exhausted
        if snapshot.turbo_utilization_pct > 95 && snapshot.standard_utilization_pct > 95 {
            return HealthStatus::Unhealthy {
                reason: "All pools exhausted".to_string(),
            };
        }

        // Warning: Turbo pool under pressure
        if snapshot.turbo_utilization_pct > 85 {
            return HealthStatus::Degraded {
                reason: "Turbo pool under pressure".to_string(),
            };
        }

        // Warning: High fallback rate
        if snapshot.turbo_fallback_count > 50 {
            return HealthStatus::Degraded {
                reason: "High Turbo fallback rate".to_string(),
            };
        }

        // Warning: Standard pool under pressure
        if snapshot.standard_utilization_pct > 85 {
            return HealthStatus::Degraded {
                reason: "Standard pool under pressure".to_string(),
            };
        }

        HealthStatus::Healthy
    }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Tests
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pool_snapshot_utilization() {
        let snapshot = PoolSnapshot {
            cached_isolates: 80,
            max_capacity: 100,
            turbo_active: 30,
            turbo_capacity: 50,
            standard_active: 10,
            standard_capacity: 50,
            turbo_utilization_pct: 60,
            standard_utilization_pct: 20,
            ..Default::default()
        };

        assert_eq!(snapshot.overall_utilization_pct(), 80);
        assert!(snapshot.is_under_pressure());
    }

    #[test]
    fn test_turbo_adoption_rate() {
        let snapshot = PoolSnapshot {
            turbo_active: 30,
            standard_active: 10,
            ..Default::default()
        };

        assert_eq!(snapshot.turbo_adoption_rate(), 75.0); // 30/(30+10) * 100
    }

    #[test]
    fn test_turbo_efficiency_score() {
        let snapshot = PoolSnapshot {
            turbo_utilization_pct: 80,
            turbo_avg_reuse_count: 100,
            ..Default::default()
        };

        assert_eq!(snapshot.turbo_efficiency_score(), 80.0); // 100 * 0.8
    }

    #[test]
    fn test_available_slots() {
        let snapshot = PoolSnapshot {
            turbo_active: 30,
            turbo_capacity: 50,
            standard_active: 40,
            standard_capacity: 50,
            ..Default::default()
        };

        assert_eq!(snapshot.turbo_available(), 20);
        assert_eq!(snapshot.standard_available(), 10);
        assert!(snapshot.has_turbo_capacity());
        assert!(snapshot.has_standard_capacity());
    }

    #[test]
    fn test_scaling_recommendations() {
        // Turbo pool needs scaling
        let snapshot1 = PoolSnapshot {
            turbo_utilization_pct: 95,
            turbo_fallback_count: 150,
            ..Default::default()
        };
        assert!(snapshot1.should_scale_turbo());

        // Standard pool needs scaling
        let snapshot2 = PoolSnapshot {
            standard_utilization_pct: 90,
            ..Default::default()
        };
        assert!(snapshot2.should_scale_standard());

        // No scaling needed
        let snapshot3 = PoolSnapshot {
            turbo_utilization_pct: 50,
            standard_utilization_pct: 50,
            turbo_fallback_count: 10,
            ..Default::default()
        };
        assert!(!snapshot3.should_scale_turbo());
        assert!(!snapshot3.should_scale_standard());
    }

    #[test]
    fn test_health_assessment() {
        // Healthy pool
        let healthy = PoolSnapshot {
            cached_isolates: 50,
            max_capacity: 100,
            turbo_utilization_pct: 50,
            standard_utilization_pct: 50,
            turbo_fallback_count: 10,
            ..Default::default()
        };
        assert_eq!(PoolHealthCheck::assess(&healthy), HealthStatus::Healthy);

        // Degraded: High Turbo utilization
        let degraded1 = PoolSnapshot {
            turbo_utilization_pct: 90,
            ..Default::default()
        };
        assert!(matches!(
            PoolHealthCheck::assess(&degraded1),
            HealthStatus::Degraded { .. }
        ));

        // Degraded: High fallback rate
        let degraded2 = PoolSnapshot {
            turbo_fallback_count: 60,
            ..Default::default()
        };
        assert!(matches!(
            PoolHealthCheck::assess(&degraded2),
            HealthStatus::Degraded { .. }
        ));

        // Unhealthy: Near capacity
        let unhealthy = PoolSnapshot {
            cached_isolates: 96,
            max_capacity: 100,
            ..Default::default()
        };
        assert!(matches!(
            PoolHealthCheck::assess(&unhealthy),
            HealthStatus::Unhealthy { .. }
        ));
    }

    #[test]
    fn test_health_status_checks() {
        let healthy = HealthStatus::Healthy;
        assert!(healthy.is_healthy());
        assert!(!healthy.is_degraded());
        assert!(!healthy.is_unhealthy());
        assert_eq!(healthy.reason(), None);

        let degraded = HealthStatus::Degraded {
            reason: "Test reason".to_string(),
        };
        assert!(!degraded.is_healthy());
        assert!(degraded.is_degraded());
        assert_eq!(degraded.reason(), Some("Test reason"));

        let unhealthy = HealthStatus::Unhealthy {
            reason: "Critical".to_string(),
        };
        assert!(unhealthy.is_unhealthy());
        assert_eq!(unhealthy.reason(), Some("Critical"));
    }

    #[test]
    fn test_serialization() {
        let snapshot = PoolSnapshot {
            cached_isolates: 50,
            max_capacity: 100,
            turbo_active: 20,
            turbo_capacity: 30,
            turbo_utilization_pct: 66,
            standard_active: 30,
            standard_capacity: 70,
            ..Default::default()
        };

        let json = serde_json::to_string(&snapshot).unwrap();
        assert!(json.contains("cached_isolates"));
        assert!(json.contains("turbo_active"));

        let deserialized: PoolSnapshot = serde_json::from_str(&json).unwrap();
        assert_eq!(deserialized.cached_isolates, 50);
        assert_eq!(deserialized.turbo_active, 20);
    }
}