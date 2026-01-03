use serde::{Deserialize, Serialize};
use std::time::Duration;
use std::path::{Path, PathBuf};

/// Tenant Service Tier (Pure Data)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum TenantTier {
    Free,
    Standard,
    Enterprise,
}

/// Resource Configuration (Pure Data)
/// 
/// # Spec-003 Compliance: Tiered Resource Allocation
/// 각 테넌트 등급에 따라 차등화된 리소스 한도를 정의합니다.
#[derive(Debug, Clone)]
pub struct ResourceConfig {
    pub heap_limit_mb: usize,
    pub max_execution_time: Duration,
    pub max_concurrent_requests: usize,
    pub cpu_quota_ms: u64,
}

/// Tenant Metadata (Pure Data)
/// 
/// # Spec-002 Compliance: Tenant Context Identification
/// 테넌트의 신원과 리소스 정책을 담는 핵심 도메인 모델입니다.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TenantMetadata {
    pub tenant_id: String,
    pub tier: TenantTier,
    pub active: bool,
    pub storage_tree: String,
    pub fs_root: String,
}

impl TenantMetadata {
    pub fn new(tenant_id: String, tier: TenantTier) -> Self {
        Self {
            storage_tree: format!("tenant_db_{}", tenant_id),
            fs_root: format!("root/tenants/{}", tenant_id),
            tenant_id,
            tier,
            active: true,
        }
    }

    /// [Pure Decision] 티어별 리소스 정책 결정
    /// 
    /// # Spec-003 Compliance: Tiered Resource Allocation
    /// - Free: 5 concurrent, 128MB heap, 100ms timeout
    /// - Standard: 20 concurrent, 256MB heap, 200ms timeout
    /// - Enterprise: 100 concurrent, 512MB heap, 500ms timeout
    pub fn resource_config(&self) -> ResourceConfig {
        match self.tier {
            TenantTier::Free => ResourceConfig {
                heap_limit_mb: 128,
                max_execution_time: Duration::from_millis(100),
                max_concurrent_requests: 5,
                cpu_quota_ms: 50,
            },
            TenantTier::Standard => ResourceConfig {
                heap_limit_mb: 256,
                max_execution_time: Duration::from_millis(200),
                max_concurrent_requests: 20,
                cpu_quota_ms: 100,
            },
            TenantTier::Enterprise => ResourceConfig {
                heap_limit_mb: 512,
                max_execution_time: Duration::from_millis(500),
                max_concurrent_requests: 100,
                cpu_quota_ms: 500,
            },
        }
    }

    /// [Pure Decision] 유효성 검증
    pub fn validate(&self) -> Result<(), TenantError> {
        if !self.active {
            return Err(TenantError::Inactive(self.tenant_id.clone()));
        }
        Ok(())
    }

    /// [Pure Decision] 경로 리매핑 로직 (Chroot 가상화의 핵심)
    /// 
    /// # Spec-002 Compliance: Virtualized Path Mapping
    /// JS에서 `/app/data/config.json` 요청 시 
    /// `root/tenants/{tenant_id}/app/data/config.json`으로 리매핑
    pub fn safe_remap(&self, virtual_path: &str) -> PathBuf {
        let clean_path = virtual_path.trim_start_matches('/');
        Path::new(&self.fs_root).join(clean_path)
    }

    /// [Pure Decision] 경로 보안 검증
    /// 
    /// # Security: Path Traversal Prevention
    /// 테넌트는 자신의 가상 루트 상위로 이동할 수 없습니다.
    pub fn is_path_allowed<P: AsRef<Path>>(&self, physical_path: P) -> bool {
        physical_path.as_ref().starts_with(&self.fs_root)
    }
}

/// [Domain Error] 테넌트 관련 에러 타입
/// 
/// # C-002 Enhancement: QuotaExceeded 추가
/// Bulkhead 패턴 적용 시 동시성 한도 초과 에러를 표현합니다.
#[derive(Debug, thiserror::Error)]
pub enum TenantError {
    #[error("Tenant {0} is inactive")]
    Inactive(String),
    
    #[error("Path access denied: {0}")]
    PathDenied(String),
    
    /// C-002: 동시성 한도 초과 에러
    /// 
    /// # Spec-003 Compliance: Concurrency & Throttling
    /// 테넌트 등급별 `max_concurrent_requests` 초과 시 발생
    #[error("Tenant {tenant_id} exceeded concurrent request quota ({current}/{max})")]
    QuotaExceeded {
        tenant_id: String,
        current: usize,
        max: usize,
    },
    
    /// 세마포어 획득 타임아웃
    #[error("Tenant {0} request timed out waiting for execution slot")]
    AcquireTimeout(String),

    /// C-003: 실행 시간 초과 (Watchdog에 의해 강제 중단)
    /// 
    /// # Spec-003 Compliance: Execution Guard (Watchdog)
    /// 테넌트 등급별 `max_execution_time` 초과 시 V8 Isolate가 강제 중단됩니다.
    /// 중단된 Isolate는 상태가 불안정하므로 풀에 반환되지 않고 폐기됩니다.
    #[error("Tenant {tenant_id} execution terminated: exceeded {limit_ms}ms time limit (ran for {elapsed_ms}ms)")]
    ExecutionTimeout {
        tenant_id: String,
        limit_ms: u64,
        elapsed_ms: u64,
    },
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tier_resource_limits() {
        let free = TenantMetadata::new("free-user".to_string(), TenantTier::Free);
        let config = free.resource_config();
        assert_eq!(config.max_concurrent_requests, 5);
        assert_eq!(config.heap_limit_mb, 128);

        let enterprise = TenantMetadata::new("ent-user".to_string(), TenantTier::Enterprise);
        let config = enterprise.resource_config();
        assert_eq!(config.max_concurrent_requests, 100);
        assert_eq!(config.heap_limit_mb, 512);
    }

    #[test]
    fn test_path_remapping() {
        let tenant = TenantMetadata::new("secure".to_string(), TenantTier::Standard);
        
        let remapped = tenant.safe_remap("/app/data.txt");
        assert_eq!(remapped, PathBuf::from("root/tenants/secure/app/data.txt"));
        
        assert!(tenant.is_path_allowed("root/tenants/secure/data/file.txt"));
        assert!(!tenant.is_path_allowed("root/tenants/other/data/file.txt"));
    }

    #[test]
    fn test_quota_exceeded_error() {
        let err = TenantError::QuotaExceeded {
            tenant_id: "test".to_string(),
            current: 5,
            max: 5,
        };
        assert!(err.to_string().contains("exceeded concurrent request quota"));
    }

    #[test]
    fn test_execution_timeout_error() {
        let err = TenantError::ExecutionTimeout {
            tenant_id: "slow-tenant".to_string(),
            limit_ms: 100,
            elapsed_ms: 150,
        };
        let msg = err.to_string();
        assert!(msg.contains("execution terminated"));
        assert!(msg.contains("100ms"));
        assert!(msg.contains("150ms"));
    }
}