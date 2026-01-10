//! Domain ↔ Protocol Type Converters
//! 
//! This module provides bidirectional conversion between domain models
//! and Protobuf messages, ensuring type safety and data integrity.
//! 
//! # Architecture
//! 
//! - Domain layer: Pure business logic types
//! - Protocol layer: Protobuf-generated types
//! - This layer: Conversion logic with comprehensive error handling
//! 
//! # Conversion Strategy
//! 
//! - Use `From`/`Into` traits for infallible conversions
//! - Use `TryFrom`/`TryInto` for fallible conversions
//! - Provide `Default` implementations for missing optional fields
//! - Never panic - use `Option` and `Default` for safety

use crate::domain::{
    TenantTier, TenantError, TransactionLog, LogStatus,
};
use super::proto::{
    KrepisContext, KrepisError, ErrorCode, ErrorCategory, ErrorMeta,
    FfiResponse, ResourceSnapshot, TURBO_SLOT_NONE,
};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// TenantTier ↔ u32 (Protocol Tier)
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/// Convert domain TenantTier to protocol u32
/// 
/// # Mapping
/// 
/// - Free = 0
/// - Standard = 1
/// - Turbo = 2
/// - Pro = 3
/// - Enterprise = 4
impl From<TenantTier> for u32 {
    fn from(tier: TenantTier) -> Self {
        tier.as_u8() as u32
    }
}

/// Convert protocol u32 to domain TenantTier
/// 
/// # Safety
/// 
/// Invalid values default to Free tier
impl From<u32> for TenantTier {
    fn from(value: u32) -> Self {
        TenantTier::from_u8(value as u8).unwrap_or(TenantTier::Free)
    }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// TenantError → KrepisError (One-way: Domain to Protocol)
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/// Convert domain TenantError to protocol ErrorCode
/// 
/// # Mapping Logic
/// 
/// Domain error codes are designed to align with protocol codes.
/// See domain/tenant/error.rs for the authoritative mapping.
impl From<&TenantError> for ErrorCode {
    fn from(error: &TenantError) -> Self {
        match error.to_proto_code() {
            // Client errors (1000-1099)
            1000 => ErrorCode::TenantNotFound,
            1001 => ErrorCode::TenantInactive,
            1003 => ErrorCode::InvalidTierUpgrade,

            // Quota errors (2000-2099)
            2000 => ErrorCode::QuotaExceeded,
            2001 => ErrorCode::AcquireTimeout,
            2002 => ErrorCode::ExecutionTimeout,
            2004 => ErrorCode::PathDenied,

            // Turbo errors (3000-3099)
            3001 => ErrorCode::TurboAllocationFailed,
            3004 => ErrorCode::TurboMemoryCorruption,

            // Internal errors (9000-9999)
            9000 => ErrorCode::Internal,

            // Unknown/unmapped errors
            _ => ErrorCode::Unknown,
        }
    }
}

/// Convert domain error category to protocol ErrorCategory
impl From<&str> for ErrorCategory {
    fn from(category: &str) -> Self {
        match category {
            "CLIENT_ERROR" => ErrorCategory::Client,
            "QUOTA_ERROR" => ErrorCategory::Throttling,
            "TURBO_ERROR" => ErrorCategory::Server,
            "INTERNAL_ERROR" => ErrorCategory::Server,
            _ => ErrorCategory::Unknown,
        }
    }
}

/// Convert domain TenantError to protocol KrepisError
/// 
/// This is the main conversion function that preserves all error metadata.
impl From<TenantError> for KrepisError {
    fn from(error: TenantError) -> Self {
        let code = ErrorCode::from(&error);
        let message = error.to_string();
        let category = ErrorCategory::from(error.to_proto_category());
        let retryable = error.is_recoverable();

        // Build error metadata
        let meta = Some(ErrorMeta {
            retryable,
            category: category as i32,
            retry_after_ms: if retryable { 1000 } else { 0 }, // 1s default retry
            attempt: 0,
            max_attempts: if retryable { 3 } else { 0 },
            resource_snapshot: None, // To be filled by caller if needed
            extensions: Default::default(),
        });

        KrepisError {
            code: code as i32,
            message,
            meta,
            tenant_id: String::new(), // To be filled by caller
            request_id: String::new(), // To be filled by caller
            trace_id: String::new(),   // To be filled by caller
            timestamp: crate::domain::now_ms(),
            stack_trace: String::new(), // Optional
            source: "krepis-kernel".to_string(),
        }
    }
}

/// Builder pattern for KrepisError to set additional fields
impl KrepisError {
    /// Set tenant ID
    pub fn with_tenant_id(mut self, tenant_id: String) -> Self {
        self.tenant_id = tenant_id;
        self
    }

    /// Set request ID
    pub fn with_request_id(mut self, request_id: String) -> Self {
        self.request_id = request_id;
        self
    }

    /// Set trace ID
    pub fn with_trace_id(mut self, trace_id: String) -> Self {
        self.trace_id = trace_id;
        self
    }

    /// Set resource snapshot
    pub fn with_resource_snapshot(mut self, snapshot: ResourceSnapshot) -> Self {
        if let Some(ref mut meta) = self.meta {
            meta.resource_snapshot = Some(snapshot);
        }
        self
    }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// TransactionLog ↔ FfiResponse (Bidirectional)
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/// Convert domain TransactionLog to protocol FfiResponse
/// 
/// # Response Construction
/// 
/// - Success: `result = success_payload` with empty bytes
/// - Failure: `result = error` with KrepisError
impl From<TransactionLog> for FfiResponse {
    fn from(log: TransactionLog) -> Self {
        let request_id = log.request_id.clone();
        let duration_us = log.duration_us.unwrap_or(0);

        // Build response based on success/failure
        let result = if log.is_success() {
            // Success case: return empty payload
            // Actual payload should be provided separately by caller
            Some(super::proto::ffi_response::Result::SuccessPayload(Vec::new()))
        } else {
            // Failure case: convert error
            let error = if let Some(err_msg) = log.error_message {
                let code = log.error_code.unwrap_or(9000); // Default to internal error
                
                // Build error from log data
                KrepisError {
                    code: match code {
                        1000 => ErrorCode::TenantNotFound as i32,
                        1001 => ErrorCode::TenantInactive as i32,
                        2000 => ErrorCode::QuotaExceeded as i32,
                        2001 => ErrorCode::AcquireTimeout as i32,
                        2002 => ErrorCode::ExecutionTimeout as i32,
                        3001 => ErrorCode::TurboAllocationFailed as i32,
                        3004 => ErrorCode::TurboMemoryCorruption as i32,
                        _ => ErrorCode::Internal as i32,
                    },
                    message: err_msg,
                    meta: Some(ErrorMeta {
                        retryable: false, // Determined by error type
                        category: ErrorCategory::Server as i32,
                        ..Default::default()
                    }),
                    tenant_id: log.tenant_id,
                    request_id: log.request_id.clone(),
                    trace_id: String::new(),
                    timestamp: log.timestamp,
                    stack_trace: String::new(),
                    source: "krepis-kernel".to_string(),
                }
            } else {
                // Generic unknown error
                KrepisError {
                    code: ErrorCode::Unknown as i32,
                    message: format!("Operation failed: {:?}", log.status),
                    ..Default::default()
                }
            };

            Some(super::proto::ffi_response::Result::Error(error))
        };

        FfiResponse {
            result,
            request_id,
            trace_id: String::new(),
            duration_us,
            protocol_version: super::proto::PROTOCOL_VERSION,
        }
    }
}

/// Builder pattern for FfiResponse to set payload
impl FfiResponse {
    /// Set success payload
    pub fn with_payload(mut self, payload: Vec<u8>) -> Self {
        if let Some(super::proto::ffi_response::Result::SuccessPayload(_)) = self.result {
            self.result = Some(super::proto::ffi_response::Result::SuccessPayload(payload));
        }
        self
    }

    /// Set trace ID
    pub fn with_trace_id(mut self, trace_id: String) -> Self {
        self.trace_id = trace_id;
        self
    }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// KrepisContext Helper Methods
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

impl KrepisContext {
    /// Create a new context for Standard FFI execution
    /// 
    /// # Arguments
    /// 
    /// * `request_id` - Unique request identifier
    /// * `tenant_id` - Tenant identifier
    /// * `tier` - Tenant tier
    pub fn new_standard(request_id: String, tenant_id: String, tier: TenantTier) -> Self {
        Self {
            request_id,
            tenant_id,
            priority: 0,
            is_turbo_mode: false,
            trace_id: String::new(),
            timestamp: crate::domain::now_ms(),
            metadata: Default::default(),
            tier: u32::from(tier),
            turbo_slot: TURBO_SLOT_NONE,
        }
    }

    /// Create a new context for Turbo zero-copy execution
    /// 
    /// # Arguments
    /// 
    /// * `request_id` - Unique request identifier
    /// * `tenant_id` - Tenant identifier
    /// * `tier` - Tenant tier (must be Turbo+)
    /// * `slot_index` - Physical slot index in shared memory
    pub fn new_turbo(
        request_id: String,
        tenant_id: String,
        tier: TenantTier,
        slot_index: u32,
    ) -> Self {
        Self {
            request_id,
            tenant_id,
            priority: 0,
            is_turbo_mode: true,
            trace_id: String::new(),
            timestamp: crate::domain::now_ms(),
            metadata: Default::default(),
            tier: u32::from(tier),
            turbo_slot: slot_index,
        }
    }

    /// Get tier as domain type
    pub fn get_tier(&self) -> TenantTier {
        TenantTier::from(self.tier)
    }

    /// Check if context uses Turbo acceleration
    pub fn uses_turbo(&self) -> bool {
        self.is_turbo_mode && self.turbo_slot != TURBO_SLOT_NONE
    }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Tests
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tenant_tier_conversion() {
        // Domain to Protocol
        assert_eq!(u32::from(TenantTier::Free), 0);
        assert_eq!(u32::from(TenantTier::Standard), 1);
        assert_eq!(u32::from(TenantTier::Turbo), 2);
        assert_eq!(u32::from(TenantTier::Pro), 3);
        assert_eq!(u32::from(TenantTier::Enterprise), 4);

        // Protocol to Domain
        assert_eq!(TenantTier::from(0u32), TenantTier::Free);
        assert_eq!(TenantTier::from(2u32), TenantTier::Turbo);
        assert_eq!(TenantTier::from(4u32), TenantTier::Enterprise);

        // Invalid value defaults to Free
        assert_eq!(TenantTier::from(99u32), TenantTier::Free);
    }

    #[test]
    fn test_error_code_mapping() {
        use crate::domain::TenantError;

        let err = TenantError::NotFound("test".into());
        let code = ErrorCode::from(&err);
        assert_eq!(code, ErrorCode::TenantNotFound);

        let err = TenantError::QuotaExceeded {
            resource: "concurrency".into(),
            limit: 10,
            current: 15,
        };
        let code = ErrorCode::from(&err);
        assert_eq!(code, ErrorCode::QuotaExceeded);
    }

    #[test]
    fn test_tenant_error_to_krepis_error() {
        use crate::domain::TenantError;

        let err = TenantError::NotFound("tenant-123".into());
        let proto_err: KrepisError = err.into();

        assert_eq!(proto_err.code, ErrorCode::TenantNotFound as i32);
        assert!(!proto_err.message.is_empty());
        assert!(proto_err.meta.is_some());
        assert_eq!(proto_err.source, "krepis-kernel");
    }

    #[test]
    fn test_krepis_error_builder() {
        use crate::domain::TenantError;

        let err = TenantError::Inactive("tenant-456".into());
        let proto_err: KrepisError = err.into();

        let enriched = proto_err
            .with_tenant_id("tenant-456".into())
            .with_request_id("req-789".into())
            .with_trace_id("trace-abc".into());

        assert_eq!(enriched.tenant_id, "tenant-456");
        assert_eq!(enriched.request_id, "req-789");
        assert_eq!(enriched.trace_id, "trace-abc");
    }

    #[test]
    fn test_transaction_log_to_ffi_response_success() {
        let log = TransactionLog::new(
            "req-123".into(),
            "tenant-abc".into(),
            "execute_script".into(),
            LogStatus::Success,
        )
        .with_duration(250); // 250µs

        let response: FfiResponse = log.into();

        assert_eq!(response.request_id, "req-123");
        assert_eq!(response.duration_us, 250);
        assert!(matches!(
            response.result,
            Some(super::ffi_response::Result::SuccessPayload(_))
        ));
    }

    #[test]
    fn test_transaction_log_to_ffi_response_failure() {
        let log = TransactionLog::new(
            "req-456".into(),
            "tenant-xyz".into(),
            "execute_script".into(),
            LogStatus::Failed,
        )
        .with_error("Runtime error".into(), Some(2004))
        .with_duration(100);

        let response: FfiResponse = log.into();

        assert_eq!(response.request_id, "req-456");
        assert_eq!(response.duration_us, 100);
        assert!(matches!(
            response.result,
            Some(super::proto::ffi_response::Result::Error(_))
        ));
    }

    #[test]
    fn test_krepis_context_standard() {
        let ctx = KrepisContext::new_standard(
            "req-111".into(),
            "tenant-222".into(),
            TenantTier::Standard,
        );

        assert_eq!(ctx.request_id, "req-111");
        assert_eq!(ctx.tenant_id, "tenant-222");
        assert_eq!(ctx.tier, 1); // Standard tier
        assert!(!ctx.is_turbo_mode);
        assert_eq!(ctx.turbo_slot, TURBO_SLOT_NONE);
        assert!(!ctx.uses_turbo());
        assert_eq!(ctx.get_tier(), TenantTier::Standard);
    }

    #[test]
    fn test_krepis_context_turbo() {
        let ctx = KrepisContext::new_turbo(
            "req-333".into(),
            "tenant-444".into(),
            TenantTier::Turbo,
            42, // slot index
        );

        assert_eq!(ctx.request_id, "req-333");
        assert_eq!(ctx.tenant_id, "tenant-444");
        assert_eq!(ctx.tier, 2); // Turbo tier
        assert!(ctx.is_turbo_mode);
        assert_eq!(ctx.turbo_slot, 42);
        assert!(ctx.uses_turbo());
        assert_eq!(ctx.get_tier(), TenantTier::Turbo);
    }

    #[test]
    fn test_ffi_response_builder() {
        let log = TransactionLog::new(
            "req".into(),
            "tenant".into(),
            "op".into(),
            LogStatus::Success,
        );

        let response: FfiResponse = log.into();
        let enriched = response
            .with_payload(b"result data".to_vec())
            .with_trace_id("trace-xyz".into());

        assert_eq!(enriched.trace_id, "trace-xyz");
        if let Some(super::proto::ffi_response::Result::SuccessPayload(payload)) = enriched.result {
            assert_eq!(payload, b"result data");
        } else {
            panic!("Expected success payload");
        }
    }

    #[test]
    fn test_error_category_conversion() {
        assert_eq!(ErrorCategory::from("CLIENT_ERROR"), ErrorCategory::Client);
        assert_eq!(ErrorCategory::from("QUOTA_ERROR"), ErrorCategory::Throttling);
        assert_eq!(ErrorCategory::from("TURBO_ERROR"), ErrorCategory::Server);
        assert_eq!(ErrorCategory::from("INTERNAL_ERROR"), ErrorCategory::Server);
        assert_eq!(ErrorCategory::from("UNKNOWN"), ErrorCategory::Unknown);
    }
}