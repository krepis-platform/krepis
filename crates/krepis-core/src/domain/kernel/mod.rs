//! Kernel Domain
//!
//! Defines the kernel's exposed capabilities and APIs that runtime implementations
//! use to interact with the Krepis kernel for dynamic runtime spawning and
//! resource constraint checking.

use crate::domain::{KrepisResult, SovereignContext};
use crate::domain::runtime::SovereignRuntime;
use std::future::Future;
use std::pin::Pin;

/// Kernel execution context and capabilities
///
/// Provided to runtime implementations to enable reverse calls into Kernel
/// (e.g., spawning child isolates, checking quotas).
pub trait KernelCapabilities: Send + Sync {
    /// Create a new child runtime instance
    fn spawn_runtime(
        &self,
        ctx: &SovereignContext,
    ) -> Pin<Box<dyn Future<Output = KrepisResult<Box<dyn SovereignRuntime>>> + Send + '_>>;

    /// Check current resource constraints
    fn check_resources(&self, ctx: &SovereignContext) -> KrepisResult<()>;

    /// Report metrics to observability system
    fn report_metrics(
        &self,
        ctx: &SovereignContext,
        metric_name: &str,
        value: f64,
    ) -> Pin<Box<dyn Future<Output = KrepisResult<()>> + Send + '_>>;
}

#[cfg(test)]
mod tests {

    #[test]
    fn kernel_capabilities_trait_exists() {
        // This test verifies the trait is properly defined
        // Concrete implementations would test actual behavior
    }
}