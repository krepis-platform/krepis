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
#[derive(Debug, Clone)]
pub struct ResourceConfig {
    pub heap_limit_mb: usize,
    pub max_execution_time: Duration,
    pub max_concurrent_requests: usize,
    pub cpu_quota_ms: u64,
}

/// Tenant Metadata (Pure Data)
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
    pub fn safe_remap(&self, virtual_path: &str) -> PathBuf {
        let clean_path = virtual_path.trim_start_matches('/');
        Path::new(&self.fs_root).join(clean_path)
    }

    /// [Pure Decision] 경로 보안 검증
    pub fn is_path_allowed<P: AsRef<Path>>(&self, physical_path: P) -> bool {
        physical_path.as_ref().starts_with(&self.fs_root)
    }
}

#[derive(Debug, thiserror::Error)]
pub enum TenantError {
    #[error("Tenant {0} is inactive")]
    Inactive(String),
    #[error("Path access denied: {0}")]
    PathDenied(String),
}