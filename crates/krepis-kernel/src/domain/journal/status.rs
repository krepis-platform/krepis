//! Domain Model: Transaction Log Status
//! 
//! Execution status tracking for tenant operations.

use serde::{Deserialize, Serialize};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Log Status Enum
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/// Transaction execution status
/// 
/// This tracks the lifecycle of a tenant operation from initiation to completion.
/// 
/// # Spec Compliance
/// 
/// - Sovereign-002: Transaction audit trail
/// - Spec-008: Status code mapping for SDK
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "SCREAMING_SNAKE_CASE")]
pub enum LogStatus {
    /// Operation has been queued but not yet started
    /// 
    /// This occurs when a tenant hits their concurrency limit
    /// and must wait for a slot to become available.
    Pending,

    /// Operation is currently executing
    /// 
    /// V8 isolate is active and running tenant code.
    Running,

    /// Operation completed successfully
    /// 
    /// All execution finished without errors.
    Success,

    /// Operation completed with errors
    /// 
    /// Runtime error, timeout, or quota violation occurred.
    Failed,

    /// Operation was terminated by watchdog
    /// 
    /// Execution exceeded time limit and was forcibly stopped.
    Timeout,

    /// Operation was cancelled by user
    /// 
    /// User requested cancellation before completion.
    Cancelled,

    /// Isolate was evicted from pool
    /// 
    /// LRU eviction occurred due to memory pressure or idle timeout.
    Evicted,

    /// **Turbo-specific**: Slot allocation failed
    /// 
    /// Turbo pool was exhausted and fallback to Standard FFI occurred.
    TurboFallback,
}

impl LogStatus {
    /// Check if status represents a terminal state
    /// 
    /// # Returns
    /// 
    /// `true` if operation is complete (success or failure)
    pub fn is_terminal(self) -> bool {
        matches!(
            self,
            Self::Success | Self::Failed | Self::Timeout | Self::Cancelled | Self::Evicted
        )
    }

    /// Check if status represents a successful outcome
    /// 
    /// # Returns
    /// 
    /// `true` if operation succeeded
    pub fn is_success(self) -> bool {
        matches!(self, Self::Success)
    }

    /// Check if status represents a failure outcome
    /// 
    /// # Returns
    /// 
    /// `true` if operation failed for any reason
    pub fn is_failure(self) -> bool {
        matches!(
            self,
            Self::Failed | Self::Timeout | Self::Cancelled | Self::Evicted
        )
    }

    /// Check if status is still in progress
    /// 
    /// # Returns
    /// 
    /// `true` if operation is pending or running
    pub fn is_in_progress(self) -> bool {
        matches!(self, Self::Pending | Self::Running)
    }

    /// Check if status indicates Turbo-related event
    /// 
    /// # Returns
    /// 
    /// `true` if status is Turbo-specific
    pub fn is_turbo_related(self) -> bool {
        matches!(self, Self::TurboFallback)
    }

    /// Convert to numeric status code for Protobuf
    /// 
    /// # Returns
    /// 
    /// Status code (0-7)
    pub fn to_code(self) -> u8 {
        match self {
            Self::Pending => 0,
            Self::Running => 1,
            Self::Success => 2,
            Self::Failed => 3,
            Self::Timeout => 4,
            Self::Cancelled => 5,
            Self::Evicted => 6,
            Self::TurboFallback => 7,
        }
    }

    /// Parse status from numeric code
    /// 
    /// # Arguments
    /// 
    /// * `code` - Numeric status code (0-7)
    /// 
    /// # Returns
    /// 
    /// `Some(LogStatus)` if valid, `None` if out of range
    pub fn from_code(code: u8) -> Option<Self> {
        match code {
            0 => Some(Self::Pending),
            1 => Some(Self::Running),
            2 => Some(Self::Success),
            3 => Some(Self::Failed),
            4 => Some(Self::Timeout),
            5 => Some(Self::Cancelled),
            6 => Some(Self::Evicted),
            7 => Some(Self::TurboFallback),
            _ => None,
        }
    }

    /// Get human-readable status name
    /// 
    /// # Returns
    /// 
    /// Status name as string
    pub fn name(self) -> &'static str {
        match self {
            Self::Pending => "Pending",
            Self::Running => "Running",
            Self::Success => "Success",
            Self::Failed => "Failed",
            Self::Timeout => "Timeout",
            Self::Cancelled => "Cancelled",
            Self::Evicted => "Evicted",
            Self::TurboFallback => "TurboFallback",
        }
    }
}

impl Default for LogStatus {
    fn default() -> Self {
        Self::Pending
    }
}

impl std::fmt::Display for LogStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name())
    }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Tests
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_terminal_status() {
        assert!(LogStatus::Success.is_terminal());
        assert!(LogStatus::Failed.is_terminal());
        assert!(LogStatus::Timeout.is_terminal());
        assert!(LogStatus::Cancelled.is_terminal());
        assert!(LogStatus::Evicted.is_terminal());

        assert!(!LogStatus::Pending.is_terminal());
        assert!(!LogStatus::Running.is_terminal());
    }

    #[test]
    fn test_success_status() {
        assert!(LogStatus::Success.is_success());
        assert!(!LogStatus::Failed.is_success());
        assert!(!LogStatus::Pending.is_success());
    }

    #[test]
    fn test_failure_status() {
        assert!(LogStatus::Failed.is_failure());
        assert!(LogStatus::Timeout.is_failure());
        assert!(LogStatus::Cancelled.is_failure());
        assert!(LogStatus::Evicted.is_failure());

        assert!(!LogStatus::Success.is_failure());
        assert!(!LogStatus::Pending.is_failure());
    }

    #[test]
    fn test_in_progress_status() {
        assert!(LogStatus::Pending.is_in_progress());
        assert!(LogStatus::Running.is_in_progress());

        assert!(!LogStatus::Success.is_in_progress());
        assert!(!LogStatus::Failed.is_in_progress());
    }

    #[test]
    fn test_turbo_related() {
        assert!(LogStatus::TurboFallback.is_turbo_related());
        assert!(!LogStatus::Success.is_turbo_related());
        assert!(!LogStatus::Failed.is_turbo_related());
    }

    #[test]
    fn test_status_codes() {
        assert_eq!(LogStatus::Pending.to_code(), 0);
        assert_eq!(LogStatus::Running.to_code(), 1);
        assert_eq!(LogStatus::Success.to_code(), 2);
        assert_eq!(LogStatus::Failed.to_code(), 3);
        assert_eq!(LogStatus::Timeout.to_code(), 4);
        assert_eq!(LogStatus::Cancelled.to_code(), 5);
        assert_eq!(LogStatus::Evicted.to_code(), 6);
        assert_eq!(LogStatus::TurboFallback.to_code(), 7);
    }

    #[test]
    fn test_status_parsing() {
        assert_eq!(LogStatus::from_code(0), Some(LogStatus::Pending));
        assert_eq!(LogStatus::from_code(2), Some(LogStatus::Success));
        assert_eq!(LogStatus::from_code(7), Some(LogStatus::TurboFallback));
        assert_eq!(LogStatus::from_code(8), None);
        assert_eq!(LogStatus::from_code(255), None);
    }

    #[test]
    fn test_status_names() {
        assert_eq!(LogStatus::Success.name(), "Success");
        assert_eq!(LogStatus::TurboFallback.name(), "TurboFallback");
        assert_eq!(format!("{}", LogStatus::Failed), "Failed");
    }

    #[test]
    fn test_default_status() {
        assert_eq!(LogStatus::default(), LogStatus::Pending);
    }

    #[test]
    fn test_serialization() {
        let status = LogStatus::Success;
        let json = serde_json::to_string(&status).unwrap();
        assert_eq!(json, "\"SUCCESS\"");

        let deserialized: LogStatus = serde_json::from_str(&json).unwrap();
        assert_eq!(deserialized, LogStatus::Success);
    }

    #[test]
    fn test_all_statuses() {
        let all_statuses = [
            LogStatus::Pending,
            LogStatus::Running,
            LogStatus::Success,
            LogStatus::Failed,
            LogStatus::Timeout,
            LogStatus::Cancelled,
            LogStatus::Evicted,
            LogStatus::TurboFallback,
        ];

        for status in &all_statuses {
            // Round-trip through code
            let code = status.to_code();
            let parsed = LogStatus::from_code(code).unwrap();
            assert_eq!(*status, parsed);

            // Name should not be empty
            assert!(!status.name().is_empty());
        }
    }
}