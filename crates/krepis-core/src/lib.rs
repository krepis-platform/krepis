//! # Krepis Core
//!
//! Shared abstraction layer between Kernel and KNUL (Network Utility Link).
//! Defines FFI boundaries, context propagation contracts, error codes, and
//! network transport abstractions that form the foundation of the Krepis
//! formal verification and execution platform.
//!
//! ## Design Philosophy
//!
//! Krepis Core embodies the principle of separation of concerns through careful
//! abstraction boundaries. The kernel logic remains agnostic to transport
//! implementation details, allowing multiple backends (QUIC, HTTP/3, mock
//! transports for testing) without modification to kernel code.
//!
//! ## Module Organization
//!
//! The library is organized into logical layers that establish clear dependencies:
//!
//! - `domain`: Domain layer containing core business abstractions
//!   - `context`: Deterministic context propagation structures
//!   - `error`: Unified error types and codes for all system components
//!   - `runtime`: Runtime lifecycle and execution contracts
//!   - `resource`: Resource quota enforcement and usage tracking
//!   - `kernel`: Kernel capabilities and reverse-call interfaces
//!   - `transport`: Network transport abstraction (Abstraction Barrier)
//! - `infrastructure`: Low-level system abstractions
//!   - `abi`: Sovereign Bridge ABI v1.1.0 FFI-safe memory layouts
//!     - `primitives`: Core buffer, response, and lock state types
//!     - `shared`: Shared memory metadata for turbo-mode coordination
//!     - `config`: Protocol-specific configuration structures

pub mod domain;
pub mod infrastructure;

// Re-export domain types at crate root for primary access pattern
pub use domain::{
    ContextBuilder, KernelCapabilities, KrepisError, KrepisResult, ResourceGuard, ResourceType,
    ResourceUsage, RuntimeStats, SovereignContext, SovereignRuntime, SovereignTransport,
    TransportFactory, TransportPacket, TransportStats,
};

// Re-export ABI types from infrastructure layer at top level for convenience
pub use infrastructure::abi::{FfiBuffer, FfiLockState, FfiQuicConfig, FfiResponse, SharedMemoryMetadata};

/// Library version following semantic versioning
pub const KREPIS_CORE_VERSION: &str = "0.1.0";

/// FFI ABI version for compatibility checking across process boundaries
/// Format: (major << 16) | minor
/// Version 1.1.0: 0x00010001
pub const FFI_ABI_VERSION: u32 = 1u32 << 16 | 1u32;

#[cfg(test)]
mod lib_tests {
    use super::*;

    #[test]
    fn version_constants_defined() {
        assert!(!KREPIS_CORE_VERSION.is_empty());
        assert_eq!(FFI_ABI_VERSION, 0x00010001);
    }

    #[test]
    fn abi_types_accessible() {
        // Verify that all ABI types are re-exported at the crate root
        let _buffer = FfiBuffer::new();
        let _response = FfiResponse::success(FfiBuffer::new());
        let _config = FfiQuicConfig::new();
        let _metadata = SharedMemoryMetadata::new(1, 32, 1024);
    }

    #[test]
    fn error_types_accessible() {
        let _error = KrepisError::Internal;
    }

    #[test]
    fn domain_context_accessible() {
        // Verify that context types are re-exported at crate root
        let ctx = SovereignContext::new(
            "test-req".to_string(),
            "test-tenant".to_string(),
            "test-trace".to_string(),
        );
        assert!(ctx.is_valid());

        let ctx_built = ContextBuilder::new("builder-req")
            .tenant("builder-tenant")
            .trace("builder-trace")
            .build();
        assert!(ctx_built.is_valid());
    }

    #[test]
    fn domain_runtime_accessible() {
        // Verify that runtime types are re-exported at crate root
        let stats = RuntimeStats::new();
        assert_eq!(stats.isolate_count, 0);
        assert_eq!(stats.avg_exec_us(), 0.0);
    }

    #[test]
    fn domain_resource_accessible() {
        // Verify that resource types are re-exported at crate root
        let usage = ResourceUsage::new("tenant-test");
        assert_eq!(usage.tenant_id, "tenant-test");
        assert!(usage.is_within_free_tier());

        // Verify resource types and limits are accessible
        let cpu_limit = ResourceType::CpuMicroseconds.default_limit_free();
        assert_eq!(cpu_limit, 100_000);
    }

    #[test]
    fn domain_transport_accessible() {
        // Verify that transport types are re-exported at crate root
        let packet = TransportPacket::new(vec![1, 2, 3], 42);
        assert_eq!(packet.connection_id, 42);
        assert_eq!(packet.len(), 3);

        let stats = TransportStats::default();
        assert_eq!(stats.total_packets_received, 0);
    }
}