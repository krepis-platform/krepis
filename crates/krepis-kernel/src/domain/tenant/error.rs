//! Domain Model: Tenant Error Types
//! 
//! Business rule violations and operational failures at the domain level.
//! Infrastructure errors (V8 crashes, network failures) belong in adapters.

use super::tier::TenantTier;
use crate::infrastructure::serialization::proto::{KrepisError, ErrorMeta, ErrorCategory};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Tenant Error Types
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/// Tenant-related domain errors
/// 
/// These represent business rule violations and operational failures
/// at the domain level.
/// 
/// # Spec Compliance
/// 
/// - Spec-008: Error codes for SDK propagation
/// - Sovereign-002: Tenant isolation enforcement
/// - Sovereign-003: Quota and limit violations
#[derive(Debug, Clone, thiserror::Error)]
pub enum TenantError {
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // Client Errors (1000-1099)
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    /// Tenant does not exist or has been deleted
    #[error("Tenant not found: {0}")]
    NotFound(String),

    /// Tenant is inactive (suspended, banned, or unpaid)
    #[error("Tenant inactive: {0}")]
    Inactive(String),

    /// Invalid tenant ID format
    #[error("Invalid tenant ID: {0}")]
    InvalidId(String),

    /// Invalid tier change attempt
    #[error("Invalid tier change from {current} to {requested}")]
    InvalidTierChange {
        current: TenantTier,
        requested: TenantTier,
    },

    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // Quota/Limit Errors (2000-2099)
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    /// Quota exceeded (C-002 enforcement)
    #[error("Quota exceeded for tenant: {0}")]
    QuotaExceeded(String),

    /// Semaphore acquisition timeout (C-002 enforcement)
    #[error("Acquire timeout for tenant: {0}")]
    AcquireTimeout(String),

    /// Execution timeout (C-003 enforcement)
    #[error("Execution timeout for tenant {tenant_id}: {elapsed_ms}ms exceeded limit of {limit_ms}ms")]
    ExecutionTimeout {
        tenant_id: String,
        limit_ms: u64,
        elapsed_ms: u64,
    },

    /// V8 runtime error (adapter layer propagated)
    #[error("Runtime error: {0}")]
    RuntimeError(String),

    /// Path access denied (Spec-002 enforcement)
    #[error("Path access denied: {0}")]
    PathDenied(String),

    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // Turbo-Specific Errors (3000-3099)
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    /// Shared memory pool exhausted
    /// 
    /// This occurs when all Turbo slots are occupied and no fallback is available.
    #[error("Turbo pool exhausted for tenant {tenant_id}: {available} slots available, {required} required")]
    TurboPoolExhausted {
        tenant_id: String,
        available: usize,
        required: usize,
    },

    /// Shared memory slot in invalid state
    /// 
    /// This indicates a state machine violation in the slot lifecycle.
    #[error("Turbo slot state error for tenant {tenant_id}: expected {expected}, found {actual}")]
    TurboSlotStateError {
        tenant_id: String,
        expected: String,
        actual: String,
    },

    /// Shared memory corruption detected
    /// 
    /// This is a critical error indicating memory safety violation.
    #[error("Turbo slot corruption detected for tenant {tenant_id}: magic mismatch")]
    TurboSlotCorruption { tenant_id: String },

    /// Turbo acceleration not available for tier
    /// 
    /// User tried to access Turbo features without qualifying tier.
    #[error("Turbo acceleration not available for tenant {tenant_id} (tier: {tier})")]
    TurboNotAvailable { tenant_id: String, tier: TenantTier },

    /// Turbo slot allocation failed
    /// 
    /// This indicates a low-level memory allocation failure.
    #[error("Turbo slot allocation failed for tenant {tenant_id}: {reason}")]
    TurboAllocationFailed { tenant_id: String, reason: String },

    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // Internal Errors (9000-9999)
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    /// Generic internal error (should be rare)
    #[error("Internal error: {0}")]
    Internal(String),
}

impl TenantError {
    /// Convert to Protobuf error code (Spec-008 compliance)
    /// 
    /// # Error Code Mapping
    /// 
    /// - 1000-1099: Client errors (user-facing)
    /// - 2000-2099: Quota/limit errors
    /// - 3000-3099: Turbo-specific errors
    /// - 9000-9999: Internal errors
    /// 
    /// # Returns
    /// 
    /// Numeric error code for SDK propagation
    pub fn to_proto_code(&self) -> i32 {
        match self {
            Self::NotFound(_) => 1001,
            Self::Inactive(_) => 1002,
            Self::InvalidId(_) => 1003,
            Self::InvalidTierChange { .. } => 1004,
            
            Self::QuotaExceeded(_) => 2001,
            Self::AcquireTimeout(_) => 2002,
            Self::ExecutionTimeout { .. } => 2003,
            Self::RuntimeError(_) => 2004,
            Self::PathDenied(_) => 2005,
            
            Self::TurboPoolExhausted { .. } => 3001,
            Self::TurboSlotStateError { .. } => 3002,
            Self::TurboSlotCorruption { .. } => 3003,
            Self::TurboNotAvailable { .. } => 3004,
            Self::TurboAllocationFailed { .. } => 3005,
            
            Self::Internal(_) => 9000,
        }
    }

    /// Convert to Protobuf error category
    /// 
    /// # Returns
    /// 
    /// Error category string for structured error responses
    pub fn to_proto_category(&self) -> &'static str {
        match self {
            Self::NotFound(_) | Self::Inactive(_) | Self::InvalidId(_) | Self::InvalidTierChange { .. } => {
                "CLIENT_ERROR"
            }
            
            Self::QuotaExceeded(_) | Self::AcquireTimeout(_) | Self::ExecutionTimeout { .. } => {
                "QUOTA_EXCEEDED"
            }
            
            Self::RuntimeError(_) | Self::PathDenied(_) => "EXECUTION_ERROR",
            
            Self::TurboPoolExhausted { .. }
            | Self::TurboSlotStateError { .. }
            | Self::TurboSlotCorruption { .. }
            | Self::TurboNotAvailable { .. }
            | Self::TurboAllocationFailed { .. } => "TURBO_ERROR",
            
            Self::Internal(_) => "INTERNAL_ERROR",
        }
    }

    /// Check if error is recoverable
    /// 
    /// Recoverable errors can be retried after backoff.
    /// 
    /// # Returns
    /// 
    /// `true` if error is transient and retryable
    pub fn is_recoverable(&self) -> bool {
        matches!(
            self,
            Self::QuotaExceeded(_)
                | Self::AcquireTimeout(_)
                | Self::TurboPoolExhausted { .. }
                | Self::TurboAllocationFailed { .. }
        )
    }

    /// Check if error indicates tier upgrade needed
    /// 
    /// Used for marketing prompts to encourage upgrades.
    /// 
    /// # Returns
    /// 
    /// `true` if upgrading tier would resolve the error
    pub fn suggests_upgrade(&self) -> bool {
        matches!(
            self,
            Self::QuotaExceeded(_)
                | Self::TurboNotAvailable { .. }
                | Self::ExecutionTimeout { .. }
        )
    }

    /// Check if error is Turbo-related
    /// 
    /// # Returns
    /// 
    /// `true` if error is specific to Turbo acceleration
    pub fn is_turbo_error(&self) -> bool {
        matches!(
            self,
            Self::TurboPoolExhausted { .. }
                | Self::TurboSlotStateError { .. }
                | Self::TurboSlotCorruption { .. }
                | Self::TurboNotAvailable { .. }
                | Self::TurboAllocationFailed { .. }
        )
    }

    /// Convert to Protobuf KrepisError (full mapping)
    /// 
    /// # Arguments
    /// 
    /// * `request_id` - Request identifier for tracing
    /// * `trace_id` - Distributed trace identifier
    /// 
    /// # Returns
    /// 
    /// Protobuf error message for SDK propagation
    pub fn into_proto(self, request_id: String, trace_id: String) -> KrepisError {
        let tenant_id = self.extract_tenant_id();
        let code = self.to_proto_code();
        let category = self.to_proto_category();
        let category_enum = ErrorCategory::from_str_name(category)
            .unwrap_or(ErrorCategory::Unknown);
        let message = self.to_string();

        KrepisError {
            code, // i32
            message,
            // Spec-008: 부가 정보는 meta 필드(ErrorMeta)에 담습니다.
            meta: Some(ErrorMeta {
                category: category_enum as i32,
                retryable: self.is_recoverable(),
                // Proto 정의에 없는 필드는 extensions 맵에 담거나 제외해야 합니다.
                // 여기서는 핵심적인 retryable과 category만 우선 매핑합니다.
                ..Default::default()
            }),
            tenant_id,
            request_id,
            trace_id,
            timestamp: crate::domain::now_ms() as i64,
            stack_trace: "".to_string(), // 필요시 추가
            source: "kernel::domain".to_string(),
        }
    }

    /// Extract tenant ID from error (if available)
    /// 
    /// # Returns
    /// 
    /// Tenant ID string, or "unknown" if not available
    fn extract_tenant_id(&self) -> String {
        match self {
            Self::NotFound(id) | Self::Inactive(id) | Self::InvalidId(id) => id.clone(),
            Self::QuotaExceeded(id) | Self::AcquireTimeout(id) => id.clone(),
            Self::ExecutionTimeout { tenant_id, .. } => tenant_id.clone(),
            Self::TurboPoolExhausted { tenant_id, .. }
            | Self::TurboSlotStateError { tenant_id, .. }
            | Self::TurboSlotCorruption { tenant_id }
            | Self::TurboNotAvailable { tenant_id, .. }
            | Self::TurboAllocationFailed { tenant_id, .. } => tenant_id.clone(),
            _ => "unknown".to_string(),
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
    fn test_error_codes() {
        assert_eq!(TenantError::NotFound("x".into()).to_proto_code(), 1001);
        assert_eq!(TenantError::Inactive("x".into()).to_proto_code(), 1002);
        assert_eq!(TenantError::InvalidId("x".into()).to_proto_code(), 1003);
        
        assert_eq!(TenantError::QuotaExceeded("x".into()).to_proto_code(), 2001);
        assert_eq!(TenantError::AcquireTimeout("x".into()).to_proto_code(), 2002);
        assert_eq!(
            TenantError::ExecutionTimeout {
                tenant_id: "x".into(),
                limit_ms: 100,
                elapsed_ms: 150
            }
            .to_proto_code(),
            2003
        );
        
        assert_eq!(
            TenantError::TurboPoolExhausted {
                tenant_id: "x".into(),
                available: 0,
                required: 1
            }
            .to_proto_code(),
            3001
        );
        assert_eq!(
            TenantError::TurboSlotStateError {
                tenant_id: "x".into(),
                expected: "idle".into(),
                actual: "active".into()
            }
            .to_proto_code(),
            3002
        );
        assert_eq!(
            TenantError::TurboSlotCorruption {
                tenant_id: "x".into()
            }
            .to_proto_code(),
            3003
        );
        
        assert_eq!(TenantError::Internal("x".into()).to_proto_code(), 9000);
    }

    #[test]
    fn test_error_categories() {
        assert_eq!(
            TenantError::NotFound("x".into()).to_proto_category(),
            "CLIENT_ERROR"
        );
        assert_eq!(
            TenantError::QuotaExceeded("x".into()).to_proto_category(),
            "QUOTA_EXCEEDED"
        );
        assert_eq!(
            TenantError::RuntimeError("x".into()).to_proto_category(),
            "EXECUTION_ERROR"
        );
        assert_eq!(
            TenantError::TurboPoolExhausted {
                tenant_id: "x".into(),
                available: 0,
                required: 1
            }
            .to_proto_category(),
            "TURBO_ERROR"
        );
        assert_eq!(
            TenantError::Internal("x".into()).to_proto_category(),
            "INTERNAL_ERROR"
        );
    }

    #[test]
    fn test_error_recoverability() {
        assert!(TenantError::QuotaExceeded("x".into()).is_recoverable());
        assert!(TenantError::AcquireTimeout("x".into()).is_recoverable());
        assert!(TenantError::TurboPoolExhausted {
            tenant_id: "x".into(),
            available: 0,
            required: 1
        }
        .is_recoverable());
        
        assert!(!TenantError::NotFound("x".into()).is_recoverable());
        assert!(!TenantError::TurboSlotCorruption {
            tenant_id: "x".into()
        }
        .is_recoverable());
    }

    #[test]
    fn test_upgrade_suggestions() {
        assert!(TenantError::QuotaExceeded("x".into()).suggests_upgrade());
        assert!(TenantError::TurboNotAvailable {
            tenant_id: "x".into(),
            tier: TenantTier::Free
        }
        .suggests_upgrade());
        assert!(TenantError::ExecutionTimeout {
            tenant_id: "x".into(),
            limit_ms: 100,
            elapsed_ms: 150
        }
        .suggests_upgrade());
        
        assert!(!TenantError::NotFound("x".into()).suggests_upgrade());
        assert!(!TenantError::Internal("x".into()).suggests_upgrade());
    }

    #[test]
    fn test_turbo_error_detection() {
        assert!(TenantError::TurboPoolExhausted {
            tenant_id: "x".into(),
            available: 0,
            required: 1
        }
        .is_turbo_error());
        
        assert!(TenantError::TurboSlotStateError {
            tenant_id: "x".into(),
            expected: "idle".into(),
            actual: "active".into()
        }
        .is_turbo_error());
        
        assert!(TenantError::TurboNotAvailable {
            tenant_id: "x".into(),
            tier: TenantTier::Standard
        }
        .is_turbo_error());
        
        assert!(!TenantError::QuotaExceeded("x".into()).is_turbo_error());
        assert!(!TenantError::RuntimeError("x".into()).is_turbo_error());
    }

    #[test]
    fn test_tenant_id_extraction() {
        let err1 = TenantError::NotFound("tenant-123".into());
        assert_eq!(err1.extract_tenant_id(), "tenant-123");
        
        let err2 = TenantError::TurboPoolExhausted {
            tenant_id: "tenant-456".into(),
            available: 0,
            required: 1,
        };
        assert_eq!(err2.extract_tenant_id(), "tenant-456");
        
        let err3 = TenantError::Internal("some error".into());
        assert_eq!(err3.extract_tenant_id(), "unknown");
    }

    #[test]
    fn test_error_display() {
        let err = TenantError::TurboPoolExhausted {
            tenant_id: "test".into(),
            available: 5,
            required: 10,
        };
        let msg = format!("{}", err);
        assert!(msg.contains("Turbo pool exhausted"));
        assert!(msg.contains("test"));
        assert!(msg.contains("5"));
        assert!(msg.contains("10"));
    }
}