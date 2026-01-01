use std::time::{Duration, Instant};
use crate::domain::tenant::TenantTier;

/// [Domain] Pool Policy - 결정만 내리는 순수 로직
pub struct PoolPolicy;

impl PoolPolicy {
    /// Pingora-style: Isolate를 캐시에서 폐기할지 결정 (순수 함수)
    pub fn should_evict(last_used: Instant, max_idle_time: Duration) -> bool {
        last_used.elapsed() > max_idle_time
    }

    /// 테넌트 티어에 따른 리소스 설정 결정 (순수 함수)
    pub fn get_resource_config(tier: TenantTier) -> DomainResourceConfig {
        match tier {
            TenantTier::Free => DomainResourceConfig {
                heap_limit_mb: 128,
                max_execution_time: Duration::from_millis(100),
            },
            TenantTier::Standard => DomainResourceConfig {
                heap_limit_mb: 256,
                max_execution_time: Duration::from_millis(200),
            },
            TenantTier::Enterprise => DomainResourceConfig {
                heap_limit_mb: 512,
                max_execution_time: Duration::from_millis(500),
            },
        }
    }
}

pub struct DomainResourceConfig {
    pub heap_limit_mb: usize,
    pub max_execution_time: Duration,
}

/// [Domain] Pool State Snapshot - CQS 조회를 위한 순수 데이터 구조
#[derive(Debug, Clone)]
pub struct PoolSnapshot {
    pub cached_isolates: usize,
    pub max_capacity: usize,
    pub healthy: bool,
}