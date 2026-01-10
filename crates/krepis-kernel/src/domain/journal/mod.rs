//! Domain Module: Transaction Journaling
//! 
//! Pure business logic for transaction logging, audit trails, and execution tracking.
//! 
//! # Architecture
//! 
//! - **Model**: `TransactionLog` - Core entity for operation tracking
//! - **Status**: `LogStatus` - Execution lifecycle states
//! 
//! # Spec Compliance
//! 
//! - **Sovereign-002**: Transaction audit trail
//! - **Performance**: Zero-copy execution tracking
//! 
//! # Zero-Copy Tracking
//! 
//! This module supports tracking both Standard FFI and Turbo executions:
//! - `is_turbo` flag distinguishes execution path
//! - `turbo_slot_index` tracks physical slot allocation
//! - `turbo_memory_offset` enables direct memory debugging
//! 
//! # Example: Standard Execution
//! 
//! ```
//! use krepis_kernel::domain::journal::{TransactionLog, LogStatus};
//! 
//! let log = TransactionLog::new(
//!     "req-123".into(),
//!     "tenant-abc".into(),
//!     "execute_script".into(),
//!     LogStatus::Success,
//! )
//! .with_duration(42_000); // 42µs (typical Standard FFI)
//! 
//! assert!(!log.is_turbo_execution());
//! assert_eq!(log.latency_category(), "medium");
//! ```
//! 
//! # Example: Turbo Execution
//! 
//! ```
//! use krepis_kernel::domain::journal::{TransactionLog, LogStatus};
//! 
//! let log = TransactionLog::new_turbo(
//!     "req-456".into(),
//!     "tenant-xyz".into(),
//!     "execute_script".into(),
//!     LogStatus::Success,
//!     42,    // slot_index
//!     8192,  // memory_offset
//! )
//! .with_duration(450); // 450ns (Turbo target)
//! 
//! assert!(log.is_turbo_execution());
//! assert_eq!(log.turbo_slot_info(), Some((42, 8192)));
//! assert_eq!(log.latency_category(), "sub-microsecond");
//! ```

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Module Declarations
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

pub mod status;
pub mod model;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Public Re-exports
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

pub use status::LogStatus;
pub use model::TransactionLog;