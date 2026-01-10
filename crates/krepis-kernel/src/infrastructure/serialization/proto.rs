//! Protobuf Generated Code
//! 
//! This module includes the Protobuf-generated Rust code from build.rs.
//! 
//! # Architecture
//! 
//! - Protobuf definitions live in `proto/` directory
//! - `build.rs` compiles them using `prost-build`
//! - Generated code is placed in `OUT_DIR`
//! - This module includes that generated code
//! 
//! # Usage
//! 
//! ```ignore
//! use crate::infrastructure::serialization::proto::*;
//! 
//! let context = KrepisContext {
//!     request_id: "req-123".to_string(),
//!     tenant_id: "tenant-abc".to_string(),
//!     tier: 2, // Turbo tier
//!     ..Default::default()
//! };
//! ```

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Protobuf Generated Code Inclusion
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/// Protobuf package: krepis.core
/// 
/// Contains all message types and enums defined in:
/// - context.proto (KrepisContext, InitializeRequest, etc.)
/// - error.proto (KrepisError, ErrorCode, ErrorCategory, etc.)
pub mod core {
    // Include the Protobuf-generated code from OUT_DIR
    // This path is set by build.rs during compilation
    include!(concat!(env!("OUT_DIR"), "/krepis.core.rs"));
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Convenience Re-exports
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// Re-export all types for convenient access
pub use core::*;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Protocol Constants
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/// Current protocol version
pub const PROTOCOL_VERSION: u32 = 2;

/// Sentinel value for "no Turbo slot" (Standard FFI execution)
pub const TURBO_SLOT_NONE: u32 = 0xFFFFFFFF;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Helper Functions
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

impl KrepisContext {
    /// Check if this context is using Turbo acceleration
    /// 
    /// # Returns
    /// 
    /// `true` if turbo_slot is a valid slot index (not 0xFFFFFFFF)
    pub fn is_using_turbo(&self) -> bool {
        self.turbo_slot != TURBO_SLOT_NONE
    }

    /// Get Turbo slot index (if using Turbo)
    /// 
    /// # Returns
    /// 
    /// `Some(slot_index)` if using Turbo, `None` if Standard FFI
    pub fn get_turbo_slot(&self) -> Option<u32> {
        if self.is_using_turbo() {
            Some(self.turbo_slot)
        } else {
            None
        }
    }
}

impl KrepisError {
    /// Check if this error is retryable
    /// 
    /// # Returns
    /// 
    /// `true` if error metadata indicates retryable
    pub fn is_retryable(&self) -> bool {
        self.meta.as_ref().map(|m| m.retryable).unwrap_or(false)
    }

    /// Get error category
    /// 
    /// # Returns
    /// 
    /// Error category enum value
    pub fn get_category(&self) -> ErrorCategory {
        self.meta
            .as_ref()
            .map(|m| ErrorCategory::try_from(m.category).unwrap_or(ErrorCategory::Unknown))
            .unwrap_or(ErrorCategory::Unknown)
    }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Tests
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_turbo_slot_detection() {
        let mut context = KrepisContext::default();
        
        // Standard FFI (no Turbo)
        context.turbo_slot = TURBO_SLOT_NONE;
        assert!(!context.is_using_turbo());
        assert_eq!(context.get_turbo_slot(), None);

        // Turbo slot 0
        context.turbo_slot = 0;
        assert!(context.is_using_turbo());
        assert_eq!(context.get_turbo_slot(), Some(0));

        // Turbo slot 42
        context.turbo_slot = 42;
        assert!(context.is_using_turbo());
        assert_eq!(context.get_turbo_slot(), Some(42));
    }

    #[test]
    fn test_error_retryability() {
        let mut error = KrepisError::default();
        
        // No metadata
        assert!(!error.is_retryable());

        // With retryable metadata
        error.meta = Some(ErrorMeta {
            retryable: true,
            category: ErrorCategory::Transient as i32,
            ..Default::default()
        });
        assert!(error.is_retryable());
        assert_eq!(error.get_category(), ErrorCategory::Transient);
    }
}