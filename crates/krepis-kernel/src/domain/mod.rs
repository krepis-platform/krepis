pub mod tenant;
pub mod pool;
pub mod journal;

// 외부에서 `domain::TenantMetadata` 식으로 바로 접근하도록 Re-export
pub use tenant::{TenantMetadata, TenantTier, TenantError, ResourceConfig};
pub use pool::{PoolPolicy, PoolSnapshot, DomainResourceConfig};
pub use journal::{TransactionLog, LogStatus};

/// [Utility] 모든 도메인에서 공통으로 사용하는 시간 측정 함수
pub fn now_ms() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("Time went backwards")
        .as_millis() as i64
}