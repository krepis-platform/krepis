//! Domain Module: Resource Pool Management
//! 
//! Pure business logic for resource pooling, eviction, storage routing, and health monitoring.
//! 
//! # Architecture
//! 
//! - **Policy**: `PoolPolicy` - Business rules for resource allocation and preemption
//! - **State**: `PoolSnapshot` - Observability and metrics
//! - **Strategy**: `StorageStrategy` - Routing decision (Standard vs Turbo)
//! 
//! # Spec Compliance
//! 
//! - **Sovereign-001**: Isolate pooling and lifecycle management
//! - **Performance**: Turbo vs Standard execution path separation
//! 
//! # Zero-Copy Routing
//! 
//! This module determines which execution path to use based on tenant tier:
//! - **Standard FFI**: Free and Standard tiers (~41.5µs context sync)
//! - **Turbo Zero-Copy**: Turbo, Pro, and Enterprise tiers (<500ns context sync)
//! 
//! # Preemption Model
//! 
//! When resources are scarce, higher tiers can preempt lower tiers:
//! 
//! | Requester     | Can Preempt          |
//! |---------------|----------------------|
//! | Free          | None                 |
//! | Standard      | Free                 |
//! | Turbo         | Free, Standard       |
//! | Pro           | Free, Standard       |
//! | Enterprise    | All lower tiers      |
//! 
//! # Example: Storage Strategy Routing
//! 
//! ```
//! use krepis_kernel::domain::{TenantTier, PoolPolicy, StorageStrategy};
//! 
//! let free_tier = TenantTier::Free;
//! let strategy = PoolPolicy::determine_storage_strategy(free_tier);
//! assert_eq!(strategy, StorageStrategy::Standard); // FFI path
//! 
//! let turbo_tier = TenantTier::Turbo;
//! let strategy = PoolPolicy::determine_storage_strategy(turbo_tier);
//! assert_eq!(strategy, StorageStrategy::Turbo); // Zero-copy path
//! ```
//! 
//! # Example: Preemption Logic
//! 
//! ```
//! use krepis_kernel::domain::{TenantTier, PoolPolicy};
//! 
//! // Enterprise can preempt Free tier
//! assert!(PoolPolicy::can_preempt(TenantTier::Enterprise, TenantTier::Free));
//! 
//! // Free cannot preempt Standard
//! assert!(!PoolPolicy::can_preempt(TenantTier::Free, TenantTier::Standard));
//! 
//! // Same tier cannot preempt each other
//! assert!(!PoolPolicy::can_preempt(TenantTier::Turbo, TenantTier::Turbo));
//! ```
//! 
//! # Example: Health Monitoring
//! 
//! ```
//! use krepis_kernel::domain::{PoolSnapshot, PoolHealthCheck};
//! 
//! let snapshot = PoolSnapshot {
//!     cached_isolates: 80,
//!     max_capacity: 100,
//!     turbo_active: 45,
//!     turbo_capacity: 50,
//!     turbo_utilization_pct: 90,
//!     standard_active: 35,
//!     standard_capacity: 50,
//!     standard_utilization_pct: 70,
//!     ..Default::default()
//! };
//! 
//! let health = PoolHealthCheck::assess(&snapshot);
//! assert!(health.is_degraded()); // Turbo pool under pressure
//! 
//! assert!(snapshot.should_scale_turbo()); // Recommend scaling
//! assert_eq!(snapshot.turbo_adoption_rate(), 56.25); // 45/(45+35) * 100
//! ```

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Module Declarations
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

pub mod policy;
pub mod state;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Public Re-exports
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

pub use policy::{PoolPolicy, StorageStrategy};
pub use state::{PoolSnapshot, HealthStatus, PoolHealthCheck};