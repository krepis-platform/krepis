//! Global Runtime and State Management
//!
//! Manages global server registry and tokio runtime for FFI async operations.
//! Provides lazy-initialized singletons for thread-safe access across FFI boundaries.

use std::sync::LazyLock;
use crate::infrastructure::registry::ServerRegistry;

/// Global server registry (thread-safe)
/// Manages all active QUIC server instances
static SERVER_REGISTRY: LazyLock<ServerRegistry> = LazyLock::new(ServerRegistry::new);

/// Global tokio runtime for FFI async operations
static TOKIO_RUNTIME: LazyLock<tokio::runtime::Runtime> = LazyLock::new(|| {
    tokio::runtime::Runtime::new().expect("Failed to create tokio runtime")
});

/// Get reference to global server registry
pub fn get_registry() -> &'static ServerRegistry {
    &SERVER_REGISTRY
}

/// Get reference to global tokio runtime
pub fn get_runtime() -> &'static tokio::runtime::Runtime {
    &TOKIO_RUNTIME
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_registry_access() {
        let registry = get_registry();
        assert_eq!(registry.count(), 0);
    }

    #[test]
    fn test_runtime_access() {
        let _runtime = get_runtime();
        // Verify runtime is available
    }
}