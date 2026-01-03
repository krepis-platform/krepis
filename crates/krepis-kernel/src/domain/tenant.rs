use serde::{Deserialize, Serialize};
use std::time::Duration;
use std::path::{Path, PathBuf};
use crate::proto::{KrepisError, ErrorCode, ErrorCategory, ErrorMeta, ResourceSnapshot};

/// Tenant Service Tier (Pure Data)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum TenantTier {
    Free,
    Standard,
    Enterprise,
}

#[derive(Debug, Clone)]
pub struct ResourceConfig {
    pub heap_limit_mb: usize,
    pub max_execution_time: Duration,
    pub max_concurrent_requests: usize,
    pub cpu_quota_ms: u64,
}

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

    pub fn validate(&self) -> Result<(), TenantError> {
        if !self.active {
            return Err(TenantError::Inactive(self.tenant_id.clone()));
        }
        Ok(())
    }

    pub fn safe_remap(&self, virtual_path: &str) -> PathBuf {
        let clean_path = virtual_path.trim_start_matches('/');
        Path::new(&self.fs_root).join(clean_path)
    }

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
    
    #[error("Tenant {tenant_id} exceeded concurrent request quota ({current}/{max})")]
    QuotaExceeded {
        tenant_id: String,
        current: usize,
        max: usize,
    },
    
    #[error("Tenant {0} request timed out waiting for execution slot")]
    AcquireTimeout(String),

    #[error("Tenant {tenant_id} execution terminated: exceeded {limit_ms}ms time limit (ran for {elapsed_ms}ms)")]
    ExecutionTimeout {
        tenant_id: String,
        limit_ms: u64,
        elapsed_ms: u64,
    },

    /// V8 실행 중 발생한 런타임 에러 또는 처리되지 않은 예외
    #[error("V8 Runtime Error: {0}")]
    RuntimeError(String),

    /// 시스템 내부 결함 또는 예기치 않은 상태
    #[error("Internal Kernel Error: {0}")]
    Internal(String),
}

impl TenantError {
    /// 도메인 에러를 SDK에 전달할 Protobuf 메시지로 변환 (Spec-008 준수)
    pub fn into_proto(self, request_id: String, trace_id: String) -> KrepisError {
        // 1. 테넌트 ID 추출
        let tenant_id = match &self {
            Self::Inactive(id) | Self::AcquireTimeout(id) => id.clone(),
            Self::QuotaExceeded { tenant_id, .. } | Self::ExecutionTimeout { tenant_id, .. } => tenant_id.clone(),
            Self::RuntimeError(_) | Self::Internal(_) | Self::PathDenied(_) => "unknown".to_string(),
        };

        // 2. Protobuf 열거형 및 메타데이터 매핑
        // krepis.core.rs에 생성된 ErrorCode::Variant 및 ErrorCategory::Variant 사용
        let (code, category, retryable, retry_after_ms, resource) = match self {
            Self::QuotaExceeded { current, max, .. } => (
                ErrorCode::QuotaExceeded,
                ErrorCategory::Throttling,
                true,
                500,
                Some(ResourceSnapshot {
                    current_concurrent: current as u32,
                    max_concurrent: max as u32,
                    ..Default::default()
                }),
            ),
            Self::AcquireTimeout(_) => (
                ErrorCode::AcquireTimeout,
                ErrorCategory::Throttling,
                true,
                1000,
                None,
            ),
            Self::ExecutionTimeout { limit_ms, elapsed_ms, .. } => (
                ErrorCode::ExecutionTimeout,
                ErrorCategory::Timeout,
                false,
                0,
                Some(ResourceSnapshot {
                    limit_ms,
                    elapsed_ms,
                    ..Default::default()
                }),
            ),
            Self::Inactive(_) => (
                ErrorCode::TenantInactive,
                ErrorCategory::Client,
                false,
                0,
                None,
            ),
            Self::PathDenied(_) => (
                ErrorCode::PathDenied,
                ErrorCategory::Client,
                false,
                0,
                None,
            ),
            Self::RuntimeError(_) => (
                ErrorCode::RuntimePanic, // 또는 적절한 코드
                ErrorCategory::Client,
                false,
                0,
                None,
            ),
            Self::Internal(_) => (
                ErrorCode::Internal,
                ErrorCategory::Server,
                false,
                0,
                None,
            ),
        };

        KrepisError {
            code: code as i32, // Protobuf enum은 i32로 캐스팅하여 저장
            message: self.to_string(),
            meta: Some(ErrorMeta {
                retryable,
                category: category as i32,
                retry_after_ms,
                resource_snapshot: resource,
                ..Default::default()
            }),
            tenant_id,
            request_id,
            trace_id,
            timestamp: crate::domain::now_ms() as i64,
            ..Default::default()
        }
    }
}