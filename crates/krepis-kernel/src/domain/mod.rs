//! Domain Layer: Pure Business Logic
//! 
//! This module contains all pure business logic, domain entities, value objects,
//! and policies. It is completely independent of infrastructure concerns.
//! 
//! # Architecture Principles
//! 
//! - **Pure Functions**: All business logic is expressed as pure functions
//! - **No Infrastructure**: No dependencies on V8, tokio, deno_core, or network
//! - **Type Safety**: Strong typing with explicit error handling
//! - **Testability**: All logic is unit-testable without mocks
//! 
//! # Module Structure
//! 
//! - `tenant`: Tenant identity, tiers, and resource policies
//! - `pool`: Resource pooling strategies and health monitoring
//! - `journal`: Transaction logging and audit trail
//! 
//! # Zero-Copy Readiness
//! 
//! This domain layer is designed to support both:
//! - **Standard FFI**: Protobuf serialization (~41.5µs)
//! - **Turbo Acceleration**: Shared memory zero-copy (<500ns)
//! 
//! The decision is made at domain level via `TenantTier::uses_turbo_acceleration()`,
//! and routing is handled by `PoolPolicy::determine_storage_strategy()`.

use std::time::{SystemTime, UNIX_EPOCH};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Module Declarations
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

pub mod tenant;
pub mod pool;
pub mod journal;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Flattened Public API (Convenience Re-exports)
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

// Tenant types
pub use tenant::{
    TenantTier,
    TenantMetadata,
    TenantError,
    ResourceConfig,
    PathPolicy,
    ResourcePolicy,
    TierRecommendationPolicy,
};

// Pool types
pub use pool::{
    PoolPolicy,
    PoolSnapshot,
    StorageStrategy,
    HealthStatus,
    PoolHealthCheck,
};

// Journal types
pub use journal::{
    TransactionLog,
    LogStatus,
};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Domain Utilities
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/// Get current timestamp in milliseconds since UNIX epoch
/// 
/// This is a pure utility function used across the domain layer
/// for consistent timestamp generation.
/// 
/// # Returns
/// 
/// Current time in milliseconds (i64)
/// 
/// # Example
/// 
/// ```
/// use krepis_kernel::domain::now_ms;
/// 
/// let timestamp = now_ms();
/// assert!(timestamp > 0);
/// ```
#[inline]
pub fn now_ms() -> i64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("System time before UNIX epoch")
        .as_millis() as i64
}

/// Get current timestamp in microseconds since UNIX epoch
/// 
/// Used for high-precision timing measurements, particularly
/// for Turbo acceleration latency tracking.
/// 
/// # Returns
/// 
/// Current time in microseconds (i64)
#[inline]
pub fn now_us() -> i64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("System time before UNIX epoch")
        .as_micros() as i64
}

/// Get current timestamp in nanoseconds since UNIX epoch
/// 
/// Used for ultra-precise timing measurements, particularly
/// for zero-copy shared memory synchronization tracking.
/// 
/// # Returns
/// 
/// Current time in nanoseconds (i64)
#[inline]
pub fn now_ns() -> i64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("System time before UNIX epoch")
        .as_nanos() as i64
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Domain Constants
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/// Default pool size for resource pooling
pub const DEFAULT_POOL_SIZE: usize = 100;

/// Default idle timeout for pooled resources (5 minutes)
pub const DEFAULT_IDLE_TIMEOUT_SECS: u64 = 300;

/// Turbo acceleration latency target (nanoseconds)
/// 
/// Zero-copy shared memory should achieve <500ns context sync
pub const TURBO_LATENCY_TARGET_NS: u64 = 500;

/// Standard FFI latency baseline (nanoseconds)
/// 
/// Protobuf FFI typically achieves ~41.5µs context sync
pub const STANDARD_LATENCY_BASELINE_NS: u64 = 41_500;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Tests
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_now_ms() {
        let t1 = now_ms();
        std::thread::sleep(std::time::Duration::from_millis(10));
        let t2 = now_ms();

        assert!(t2 > t1);
        assert!(t2 - t1 >= 10); // At least 10ms passed
    }

    #[test]
    fn test_now_us() {
        let t1 = now_us();
        std::thread::sleep(std::time::Duration::from_micros(100));
        let t2 = now_us();

        assert!(t2 > t1);
        assert!(t2 - t1 >= 100); // At least 100µs passed
    }

    #[test]
    fn test_now_ns() {
        let t1 = now_ns();
        let t2 = now_ns();

        assert!(t2 >= t1); // Time moves forward (or equal if very fast)
    }

    #[test]
    fn test_timestamp_ordering() {
        let ms = now_ms();
        let us = now_us();
        let ns = now_ns();

        // Microseconds should be larger than milliseconds (different scale)
        assert!(us > ms);
        // Nanoseconds should be larger than microseconds (different scale)
        assert!(ns > us);
    }

    #[test]
    fn test_domain_exports() {
        // Test that all major types are accessible at domain root
        let _tier: TenantTier = TenantTier::Free;
        let _tenant = TenantMetadata::new("test".into(), TenantTier::Standard);
        let _strategy = StorageStrategy::Standard;
        let _status = LogStatus::Pending;
    }

    #[test]
    fn test_constants() {
        assert_eq!(DEFAULT_POOL_SIZE, 100);
        assert_eq!(DEFAULT_IDLE_TIMEOUT_SECS, 300);
        assert_eq!(TURBO_LATENCY_TARGET_NS, 500);
        assert_eq!(STANDARD_LATENCY_BASELINE_NS, 41_500);

        // Turbo should be ~80x faster than Standard
        let speedup = STANDARD_LATENCY_BASELINE_NS / TURBO_LATENCY_TARGET_NS;
        assert_eq!(speedup, 83);
    }
}