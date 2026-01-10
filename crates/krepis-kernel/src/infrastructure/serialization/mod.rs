//! Infrastructure Layer: Serialization
//! 
//! This module handles all serialization concerns between domain models
//! and wire protocol (Protobuf), providing a clean abstraction layer.
//! 
//! # Architecture
//! 
//! ```text
//! ┌─────────────────────────────────────────────────────────────┐
//! │                    Domain Layer (Pure)                      │
//! │  TenantTier, TenantError, TransactionLog, PoolSnapshot      │
//! └───────────────────────────┬─────────────────────────────────┘
//!                             │
//!                   ┌─────────▼─────────┐
//!                   │   converters.rs   │ ◄─── Domain ↔ Proto
//!                   └─────────┬─────────┘
//!                             │
//! ┌───────────────────────────▼─────────────────────────────────┐
//! │                  Protocol Layer (Protobuf)                  │
//! │    KrepisContext, KrepisError, FfiResponse, FfiEnvelope     │
//! └─────────────────────────────────────────────────────────────┘
//! ```
//! 
//! # Module Structure
//! 
//! - **proto**: Generated Protobuf code (from build.rs)
//! - **converters**: Domain ↔ Protocol type conversions
//! - **mod** (this file): Public API and utilities
//! 
//! # Usage Example: Context Creation
//! 
//! ```ignore
//! use krepis_kernel::infrastructure::serialization::*;
//! use krepis_kernel::domain::TenantTier;
//! 
//! // Create Standard FFI context
//! let ctx = KrepisContext::new_standard(
//!     "req-123".into(),
//!     "tenant-abc".into(),
//!     TenantTier::Standard,
//! );
//! 
//! // Create Turbo zero-copy context
//! let ctx = KrepisContext::new_turbo(
//!     "req-456".into(),
//!     "tenant-xyz".into(),
//!     TenantTier::Turbo,
//!     42, // slot_index
//! );
//! ```
//! 
//! # Usage Example: Error Conversion
//! 
//! ```ignore
//! use krepis_kernel::infrastructure::serialization::*;
//! use krepis_kernel::domain::TenantError;
//! 
//! let domain_error = TenantError::QuotaExceeded {
//!     resource: "concurrency".into(),
//!     limit: 10,
//!     current: 15,
//! };
//! 
//! let proto_error: KrepisError = domain_error.into();
//! let enriched = proto_error
//!     .with_tenant_id("tenant-123".into())
//!     .with_request_id("req-456".into());
//! ```
//! 
//! # Usage Example: Response Building
//! 
//! ```ignore
//! use krepis_kernel::infrastructure::serialization::*;
//! use krepis_kernel::domain::{TransactionLog, LogStatus};
//! 
//! let log = TransactionLog::new(
//!     "req-789".into(),
//!     "tenant-abc".into(),
//!     "execute_script".into(),
//!     LogStatus::Success,
//! ).with_duration(250);
//! 
//! let response: FfiResponse = log.into();
//! let final_response = response
//!     .with_payload(b"result data".to_vec())
//!     .with_trace_id("trace-xyz".into());
//! ```

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Module Declarations
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

pub mod proto;
pub mod converters;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Public API (Flattened Re-exports)
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// Protocol types
pub use proto::{
    KrepisContext,
    KrepisError,
    ErrorCode,
    ErrorCategory,
    ErrorMeta,
    FfiResponse,
    FfiEnvelope,
    MessageType,
    ResourceSnapshot,
    InitializeRequest,
    InitializeResponse,
    KnulConfig,
    PROTOCOL_VERSION,
    TURBO_SLOT_NONE,
};

// Conversion traits are automatically available via the blanket implementations
// in converters.rs, so we don't need to re-export them explicitly.

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Serialization Utilities
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

use prost::Message;
use anyhow::{Result, Context as AnyhowContext};

/// Serialize a Protobuf message to bytes
/// 
/// # Arguments
/// 
/// * `message` - Any Protobuf message implementing `prost::Message`
/// 
/// # Returns
/// 
/// Serialized bytes, or error if encoding fails
/// 
/// # Example
/// 
/// ```ignore
/// let ctx = KrepisContext::new_standard(...);
/// let bytes = serialize(&ctx)?;
/// ```
pub fn serialize<M: Message>(message: &M) -> Result<Vec<u8>> {
    let mut buf = Vec::with_capacity(message.encoded_len());
    message
        .encode(&mut buf)
        .context("Failed to encode Protobuf message")?;
    Ok(buf)
}

/// Deserialize bytes into a Protobuf message
/// 
/// # Arguments
/// 
/// * `bytes` - Serialized Protobuf bytes
/// 
/// # Returns
/// 
/// Deserialized message, or error if decoding fails
/// 
/// # Example
/// 
/// ```ignore
/// let ctx: KrepisContext = deserialize(&bytes)?;
/// ```
pub fn deserialize<M: Message + Default>(bytes: &[u8]) -> Result<M> {
    M::decode(bytes).context("Failed to decode Protobuf message")
}

/// Create an FfiEnvelope for a message
/// 
/// # Arguments
/// 
/// * `message_type` - Type of message being wrapped
/// * `payload` - Serialized message bytes
/// 
/// # Returns
/// 
/// FfiEnvelope ready for transmission
/// 
/// # Example
/// 
/// ```ignore
/// let ctx = KrepisContext::new_standard(...);
/// let payload = serialize(&ctx)?;
/// let envelope = create_envelope(MessageType::Context, payload);
/// ```
pub fn create_envelope(message_type: MessageType, payload: Vec<u8>) -> FfiEnvelope {
    FfiEnvelope {
        protocol_version: PROTOCOL_VERSION,
        message_type: message_type as i32,
        payload,
        extensions: Default::default(),
    }
}

/// Extract payload from an FfiEnvelope
/// 
/// # Arguments
/// 
/// * `envelope` - FfiEnvelope containing wrapped message
/// 
/// # Returns
/// 
/// Payload bytes and message type
/// 
/// # Example
/// 
/// ```ignore
/// let (msg_type, payload) = extract_payload(&envelope)?;
/// let ctx: KrepisContext = deserialize(&payload)?;
/// ```
pub fn extract_payload(envelope: &FfiEnvelope) -> Result<(MessageType, &[u8])> {
    let msg_type = MessageType::try_from(envelope.message_type)
        .unwrap_or(MessageType::Unknown);
    Ok((msg_type, &envelope.payload))
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Tests
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

#[cfg(test)]
mod tests {
    use super::*;
    use crate::domain::TenantTier;

    #[test]
    fn test_serialize_deserialize_context() {
        let original = KrepisContext::new_standard(
            "req-123".into(),
            "tenant-abc".into(),
            TenantTier::Standard,
        );

        // Serialize
        let bytes = serialize(&original).unwrap();
        assert!(!bytes.is_empty());

        // Deserialize
        let deserialized: KrepisContext = deserialize(&bytes).unwrap();
        assert_eq!(deserialized.request_id, original.request_id);
        assert_eq!(deserialized.tenant_id, original.tenant_id);
        assert_eq!(deserialized.tier, original.tier);
    }

    #[test]
    fn test_envelope_creation() {
        let ctx = KrepisContext::new_turbo(
            "req-456".into(),
            "tenant-xyz".into(),
            TenantTier::Turbo,
            42,
        );

        let payload = serialize(&ctx).unwrap();
        let envelope = create_envelope(MessageType::Context, payload);

        assert_eq!(envelope.protocol_version, PROTOCOL_VERSION);
        assert_eq!(envelope.message_type, MessageType::Context as i32);
        assert!(!envelope.payload.is_empty());
    }

    #[test]
    fn test_envelope_extraction() {
        let ctx = KrepisContext::new_standard(
            "req-789".into(),
            "tenant-111".into(),
            TenantTier::Free,
        );

        let payload = serialize(&ctx).unwrap();
        let envelope = create_envelope(MessageType::Context, payload);

        // Extract and deserialize
        let (msg_type, extracted_payload) = extract_payload(&envelope).unwrap();
        assert_eq!(msg_type, MessageType::Context);

        let deserialized: KrepisContext = deserialize(extracted_payload).unwrap();
        assert_eq!(deserialized.request_id, "req-789");
        assert_eq!(deserialized.tenant_id, "tenant-111");
    }

    #[test]
    fn test_error_conversion_roundtrip() {
        use crate::domain::TenantError;

        let domain_error = TenantError::QuotaExceeded {
            resource: "memory".into(),
            limit: 100,
            current: 150,
        };

        let proto_error: KrepisError = domain_error.into();
        let enriched = proto_error
            .with_tenant_id("tenant-222".into())
            .with_request_id("req-333".into());

        // Serialize and deserialize
        let bytes = serialize(&enriched).unwrap();
        let deserialized: KrepisError = deserialize(&bytes).unwrap();

        assert_eq!(deserialized.tenant_id, "tenant-222");
        assert_eq!(deserialized.request_id, "req-333");
        assert_eq!(deserialized.code, ErrorCode::QuotaExceeded as i32);
    }

    #[test]
    fn test_ffi_response_success() {
        use crate::domain::{TransactionLog, LogStatus};

        let log = TransactionLog::new(
            "req-success".into(),
            "tenant-test".into(),
            "test_op".into(),
            LogStatus::Success,
        )
        .with_duration(250);

        let response: FfiResponse = log.into();
        let final_response = response
            .with_payload(b"test result".to_vec())
            .with_trace_id("trace-123".into());

        // Serialize and deserialize
        let bytes = serialize(&final_response).unwrap();
        let deserialized: FfiResponse = deserialize(&bytes).unwrap();

        assert_eq!(deserialized.request_id, "req-success");
        assert_eq!(deserialized.duration_us, 250);
        assert_eq!(deserialized.trace_id, "trace-123");

        // Check success payload
        if let Some(proto::ffi_response::Result::SuccessPayload(payload)) = deserialized.result {
            assert_eq!(payload, b"test result");
        } else {
            panic!("Expected success payload");
        }
    }

    #[test]
    fn test_ffi_response_error() {
        use crate::domain::{TransactionLog, LogStatus};

        let log = TransactionLog::new(
            "req-error".into(),
            "tenant-test".into(),
            "test_op".into(),
            LogStatus::Failed,
        )
        .with_error("Test error".into(), Some(9000))
        .with_duration(100);

        let response: FfiResponse = log.into();

        // Serialize and deserialize
        let bytes = serialize(&response).unwrap();
        let deserialized: FfiResponse = deserialize(&bytes).unwrap();

        assert_eq!(deserialized.request_id, "req-error");
        assert_eq!(deserialized.duration_us, 100);

        // Check error payload
        assert!(matches!(
            deserialized.result,
            Some(proto::ffi_response::Result::Error(_))
        ));
    }

    #[test]
    fn test_turbo_context_serialization() {
        let turbo_ctx = KrepisContext::new_turbo(
            "req-turbo".into(),
            "tenant-turbo".into(),
            TenantTier::Enterprise,
            99, // slot index
        );

        assert!(turbo_ctx.uses_turbo());
        assert_eq!(turbo_ctx.get_turbo_slot(), Some(99));

        // Serialize and deserialize
        let bytes = serialize(&turbo_ctx).unwrap();
        let deserialized: KrepisContext = deserialize(&bytes).unwrap();

        assert!(deserialized.is_turbo_mode);
        assert_eq!(deserialized.turbo_slot, 99);
        assert_eq!(deserialized.tier, 4); // Enterprise
        assert!(deserialized.uses_turbo());
    }

    #[test]
    fn test_protocol_version_constant() {
        assert_eq!(PROTOCOL_VERSION, 2);
    }

    #[test]
    fn test_turbo_slot_none_constant() {
        assert_eq!(TURBO_SLOT_NONE, 0xFFFFFFFF);
        
        let std_ctx = KrepisContext::new_standard(
            "req".into(),
            "tenant".into(),
            TenantTier::Standard,
        );
        assert_eq!(std_ctx.turbo_slot, TURBO_SLOT_NONE);
    }
}