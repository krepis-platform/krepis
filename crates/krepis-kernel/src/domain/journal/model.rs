//! Domain Model: Transaction Log
//! 
//! Audit trail for tenant operations with Zero-copy tracking support.

use serde::{Deserialize, Serialize};

use super::status::LogStatus;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Transaction Log Model
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/// Transaction log entry for tenant operations
/// 
/// This provides a complete audit trail of all tenant executions,
/// including performance metrics and Zero-copy acceleration metadata.
/// 
/// # Spec Compliance
/// 
/// - Sovereign-002: Transaction journaling
/// - Performance: Turbo acceleration tracking
/// 
/// # Zero-Copy Fields
/// 
/// - `is_turbo`: Whether this execution used Turbo acceleration
/// - `turbo_slot_index`: Physical slot index in shared memory pool (if Turbo)
/// - `turbo_memory_offset`: Memory offset for zero-copy context (if Turbo)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TransactionLog {
    /// Unique request identifier
    pub request_id: String,

    /// Tenant identifier
    pub tenant_id: String,

    /// Operation name (e.g., "execute_script", "op_increment_stats")
    pub op_name: String,

    /// Execution status
    pub status: LogStatus,

    /// Timestamp when operation started (milliseconds since UNIX epoch)
    pub timestamp: i64,

    /// Duration of execution in microseconds
    /// 
    /// For Turbo executions, this includes the zero-copy context sync time.
    pub duration_us: Option<u64>,

    /// **Zero-Copy Flag**
    /// 
    /// `true` if this execution used Turbo shared memory acceleration.
    /// `false` if this execution used Standard FFI with Protobuf.
    /// 
    /// # Performance Tracking
    /// 
    /// This flag allows us to measure the effectiveness of Turbo acceleration:
    /// - Turbo executions should have `duration_us` <500ns for context sync
    /// - Standard executions typically have ~41.5µs for context sync
    pub is_turbo: bool,

    /// **Turbo Slot Index**
    /// 
    /// Physical slot index in the shared memory pool (0-N).
    /// Only present if `is_turbo = true`.
    /// 
    /// # Use Cases
    /// 
    /// - Debugging memory corruption issues
    /// - Identifying hot slots (frequently reused)
    /// - Tracking slot lifecycle for performance analysis
    #[serde(skip_serializing_if = "Option::is_none")]
    pub turbo_slot_index: Option<usize>,

    /// **Turbo Memory Offset**
    /// 
    /// Byte offset into the shared memory region where this context resides.
    /// Only present if `is_turbo = true`.
    /// 
    /// # Use Cases
    /// 
    /// - Direct memory debugging
    /// - Verifying cache alignment
    /// - Memory leak detection
    #[serde(skip_serializing_if = "Option::is_none")]
    pub turbo_memory_offset: Option<usize>,

    /// Error message (if status = Failed/Timeout)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error_message: Option<String>,

    /// Error code (if status = Failed)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error_code: Option<i32>,
}

impl TransactionLog {
    /// Create a new transaction log entry
    /// 
    /// # Arguments
    /// 
    /// * `request_id` - Unique request identifier
    /// * `tenant_id` - Tenant identifier
    /// * `op_name` - Operation name
    /// * `status` - Execution status
    /// 
    /// # Returns
    /// 
    /// New transaction log with current timestamp
    pub fn new(
        request_id: String,
        tenant_id: String,
        op_name: String,
        status: LogStatus,
    ) -> Self {
        Self {
            request_id,
            tenant_id,
            op_name,
            status,
            timestamp: crate::domain::now_ms(),
            duration_us: None,
            is_turbo: false,
            turbo_slot_index: None,
            turbo_memory_offset: None,
            error_message: None,
            error_code: None,
        }
    }

    /// Create a Turbo-accelerated transaction log entry
    /// 
    /// # Arguments
    /// 
    /// * `request_id` - Unique request identifier
    /// * `tenant_id` - Tenant identifier
    /// * `op_name` - Operation name
    /// * `status` - Execution status
    /// * `slot_index` - Physical slot index in shared memory
    /// * `memory_offset` - Byte offset into shared memory
    /// 
    /// # Returns
    /// 
    /// New transaction log with Turbo metadata
    pub fn new_turbo(
        request_id: String,
        tenant_id: String,
        op_name: String,
        status: LogStatus,
        slot_index: usize,
        memory_offset: usize,
    ) -> Self {
        Self {
            request_id,
            tenant_id,
            op_name,
            status,
            timestamp: crate::domain::now_ms(),
            duration_us: None,
            is_turbo: true,
            turbo_slot_index: Some(slot_index),
            turbo_memory_offset: Some(memory_offset),
            error_message: None,
            error_code: None,
        }
    }

    /// Set execution duration
    /// 
    /// # Arguments
    /// 
    /// * `duration_us` - Duration in microseconds
    pub fn with_duration(mut self, duration_us: u64) -> Self {
        self.duration_us = Some(duration_us);
        self
    }

    /// Set error information
    /// 
    /// # Arguments
    /// 
    /// * `message` - Error message
    /// * `code` - Error code (optional)
    pub fn with_error(mut self, message: String, code: Option<i32>) -> Self {
        self.error_message = Some(message);
        self.error_code = code;
        self
    }

    /// Check if this log represents a Turbo execution
    /// 
    /// # Returns
    /// 
    /// `true` if Turbo acceleration was used
    #[inline]
    pub fn is_turbo_execution(&self) -> bool {
        self.is_turbo
    }

    /// Get Turbo slot information (if available)
    /// 
    /// # Returns
    /// 
    /// `Some((slot_index, memory_offset))` if Turbo, `None` otherwise
    pub fn turbo_slot_info(&self) -> Option<(usize, usize)> {
        match (self.turbo_slot_index, self.turbo_memory_offset) {
            (Some(idx), Some(offset)) => Some((idx, offset)),
            _ => None,
        }
    }

    /// Check if execution was successful
    /// 
    /// # Returns
    /// 
    /// `true` if status is Success
    #[inline]
    pub fn is_success(&self) -> bool {
        self.status.is_success()
    }

    /// Check if execution failed
    /// 
    /// # Returns
    /// 
    /// `true` if status indicates failure
    #[inline]
    pub fn is_failure(&self) -> bool {
        self.status.is_failure()
    }

    /// Get execution duration in microseconds
    /// 
    /// # Returns
    /// 
    /// Duration if available, `None` if operation is still in progress
    pub fn duration_us(&self) -> Option<u64> {
        self.duration_us
    }

    /// Get execution duration in nanoseconds
    /// 
    /// # Returns
    /// 
    /// Duration in nanoseconds if available
    pub fn duration_ns(&self) -> Option<u64> {
        self.duration_us.map(|us| us * 1000)
    }

    /// Calculate latency category for monitoring
    /// 
    /// # Returns
    /// 
    /// - `"sub-microsecond"` if <1µs (Turbo target)
    /// - `"low"` if 1-10µs
    /// - `"medium"` if 10-100µs
    /// - `"high"` if >100µs
    pub fn latency_category(&self) -> &'static str {
        match self.duration_us {
            None => "unknown",
            Some(us) if us == 0 => "sub-microsecond",
            Some(us) if us < 10 => "low",
            Some(us) if us < 100 => "medium",
            _ => "high",
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
    fn test_standard_transaction_log() {
        let log = TransactionLog::new(
            "req-123".into(),
            "tenant-abc".into(),
            "execute_script".into(),
            LogStatus::Success,
        );

        assert_eq!(log.request_id, "req-123");
        assert_eq!(log.tenant_id, "tenant-abc");
        assert_eq!(log.op_name, "execute_script");
        assert_eq!(log.status, LogStatus::Success);
        assert!(!log.is_turbo);
        assert!(log.turbo_slot_index.is_none());
        assert!(log.turbo_memory_offset.is_none());
    }

    #[test]
    fn test_turbo_transaction_log() {
        let log = TransactionLog::new_turbo(
            "req-456".into(),
            "tenant-xyz".into(),
            "execute_script".into(),
            LogStatus::Success,
            42,  // slot_index
            8192, // memory_offset
        );

        assert_eq!(log.request_id, "req-456");
        assert!(log.is_turbo);
        assert_eq!(log.turbo_slot_index, Some(42));
        assert_eq!(log.turbo_memory_offset, Some(8192));
        assert!(log.is_turbo_execution());
    }

    #[test]
    fn test_turbo_slot_info() {
        let mut log = TransactionLog::new(
            "req".into(),
            "tenant".into(),
            "op".into(),
            LogStatus::Running,
        );

        // Standard execution has no slot info
        assert_eq!(log.turbo_slot_info(), None);

        // Add Turbo info
        log.is_turbo = true;
        log.turbo_slot_index = Some(10);
        log.turbo_memory_offset = Some(4096);

        assert_eq!(log.turbo_slot_info(), Some((10, 4096)));
    }

    #[test]
    fn test_with_duration() {
        let log = TransactionLog::new(
            "req".into(),
            "tenant".into(),
            "op".into(),
            LogStatus::Success,
        )
        .with_duration(250); // 250µs

        assert_eq!(log.duration_us(), Some(250));
        assert_eq!(log.duration_ns(), Some(250_000));
    }

    #[test]
    fn test_with_error() {
        let log = TransactionLog::new(
            "req".into(),
            "tenant".into(),
            "op".into(),
            LogStatus::Failed,
        )
        .with_error("Runtime error".into(), Some(2004));

        assert_eq!(log.error_message, Some("Runtime error".into()));
        assert_eq!(log.error_code, Some(2004));
    }

    #[test]
    fn test_status_checks() {
        let success_log = TransactionLog::new(
            "req".into(),
            "tenant".into(),
            "op".into(),
            LogStatus::Success,
        );
        assert!(success_log.is_success());
        assert!(!success_log.is_failure());

        let failed_log = TransactionLog::new(
            "req".into(),
            "tenant".into(),
            "op".into(),
            LogStatus::Failed,
        );
        assert!(!failed_log.is_success());
        assert!(failed_log.is_failure());
    }

    #[test]
    fn test_latency_categorization() {
        let log1 = TransactionLog::new("r".into(), "t".into(), "o".into(), LogStatus::Success)
            .with_duration(0); // sub-microsecond (Turbo)
        assert_eq!(log1.latency_category(), "sub-microsecond");

        let log2 = TransactionLog::new("r".into(), "t".into(), "o".into(), LogStatus::Success)
            .with_duration(5); // 5µs
        assert_eq!(log2.latency_category(), "low");

        let log3 = TransactionLog::new("r".into(), "t".into(), "o".into(), LogStatus::Success)
            .with_duration(50); // 50µs
        assert_eq!(log3.latency_category(), "medium");

        let log4 = TransactionLog::new("r".into(), "t".into(), "o".into(), LogStatus::Success)
            .with_duration(200); // 200µs
        assert_eq!(log4.latency_category(), "high");

        let log5 = TransactionLog::new("r".into(), "t".into(), "o".into(), LogStatus::Running);
        assert_eq!(log5.latency_category(), "unknown");
    }

    #[test]
    fn test_serialization() {
        let log = TransactionLog::new_turbo(
            "req-789".into(),
            "tenant-test".into(),
            "op_test".into(),
            LogStatus::Success,
            5,
            1024,
        )
        .with_duration(350);

        let json = serde_json::to_string(&log).unwrap();
        assert!(json.contains("req-789"));
        assert!(json.contains("turbo_slot_index"));
        assert!(json.contains("350"));

        let deserialized: TransactionLog = serde_json::from_str(&json).unwrap();
        assert_eq!(deserialized.request_id, "req-789");
        assert_eq!(deserialized.is_turbo, true);
        assert_eq!(deserialized.turbo_slot_index, Some(5));
        assert_eq!(deserialized.duration_us, Some(350));
    }

    #[test]
    fn test_optional_fields_serialization() {
        let log = TransactionLog::new(
            "req".into(),
            "tenant".into(),
            "op".into(),
            LogStatus::Success,
        );

        let json = serde_json::to_string(&log).unwrap();

        // Optional fields should be omitted
        assert!(!json.contains("turbo_slot_index"));
        assert!(!json.contains("turbo_memory_offset"));
        assert!(!json.contains("error_message"));
        assert!(!json.contains("duration_us"));
    }

    #[test]
    fn test_turbo_vs_standard_execution() {
        // Standard execution
        let standard = TransactionLog::new(
            "req-std".into(),
            "tenant".into(),
            "op".into(),
            LogStatus::Success,
        )
        .with_duration(41); // 41µs (typical Standard FFI)

        assert!(!standard.is_turbo_execution());
        assert_eq!(standard.latency_category(), "medium");

        // Turbo execution
        let turbo = TransactionLog::new_turbo(
            "req-turbo".into(),
            "tenant".into(),
            "op".into(),
            LogStatus::Success,
            0,
            0,
        )
        .with_duration(0); // <1µs (target Turbo)

        assert!(turbo.is_turbo_execution());
        assert_eq!(turbo.latency_category(), "sub-microsecond");

        // Performance comparison
        let speedup = standard.duration_us().unwrap() as f64 / 
                     (turbo.duration_us().unwrap() + 1) as f64; // Avoid div by 0
        assert!(speedup > 40.0); // Turbo should be >40x faster
    }
}