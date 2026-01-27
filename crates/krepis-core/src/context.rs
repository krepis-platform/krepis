//! # Context Propagation v1.2.0
//!
//! Core context structure that flows through entire Krepis stack.
//! Implements Deterministic Context principle: all async operations
//! and domain logic receive explicit `ctx: SovereignContext` parameter.

use serde::{Deserialize, Serialize};
use std::fmt;

/// Sovereign Context: the canonical context object passed through all kernel operations
///
/// Ensures complete traceability, deterministic behavior, and proper request scoping.
/// Must be explicitly threaded through async operations and domain functions.
///
/// # Examples
///
/// ```text
/// async fn my_handler(ctx: SovereignContext) -> Result<Response> {
///     // ctx flows explicitly through all callees
///     do_work(&ctx).await
/// }
/// ```
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SovereignContext {
    /// Unique request identifier (UUID or snowflake)
    pub request_id: String,
    /// Multi-tenant isolation scope
    pub tenant_id: String,
    /// Distributed trace correlation ID
    pub trace_id: String,
    /// Turbo-mode flag: true = shared memory FFI, false = standard FFI
    pub is_turbo_mode: bool,
    /// Request creation timestamp (Unix nanoseconds)
    pub timestamp: u64,
}

impl SovereignContext {
    /// Create a new context with generated IDs
    pub fn new(request_id: String, tenant_id: String, trace_id: String) -> Self {
        Self {
            request_id,
            tenant_id,
            trace_id,
            is_turbo_mode: false,
            timestamp: Self::current_timestamp(),
        }
    }

    /// Create a context in turbo mode (zero-copy shared memory)
    pub fn new_turbo(request_id: String, tenant_id: String, trace_id: String) -> Self {
        Self {
            request_id,
            tenant_id,
            trace_id,
            is_turbo_mode: true,
            timestamp: Self::current_timestamp(),
        }
    }

    /// Create a child context for spawned operations (maintains parent trace)
    pub fn spawn_child(&self, new_request_id: String) -> Self {
        Self {
            request_id: new_request_id,
            tenant_id: self.tenant_id.clone(),
            trace_id: self.trace_id.clone(),
            is_turbo_mode: self.is_turbo_mode,
            timestamp: Self::current_timestamp(),
        }
    }

    /// Get current system timestamp in nanoseconds
    fn current_timestamp() -> u64 {
        use std::time::{SystemTime, UNIX_EPOCH};
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_nanos() as u64)
            .unwrap_or(0)
    }

    /// Check if context is valid for request processing
    pub fn is_valid(&self) -> bool {
        !self.request_id.is_empty() && !self.tenant_id.is_empty() && !self.trace_id.is_empty()
    }

    /// Elapsed time since context creation (nanoseconds)
    pub fn elapsed_ns(&self) -> u64 {
        Self::current_timestamp().saturating_sub(self.timestamp)
    }
}

impl fmt::Display for SovereignContext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "SovereignContext {{ req_id: {}, tenant: {}, trace: {}, turbo: {}, ts: {} }}",
            self.request_id, self.tenant_id, self.trace_id, self.is_turbo_mode, self.timestamp
        )
    }
}

impl Default for SovereignContext {
    fn default() -> Self {
        Self {
            request_id: "default".to_string(),
            tenant_id: "default".to_string(),
            trace_id: "default".to_string(),
            is_turbo_mode: false,
            timestamp: 0,
        }
    }
}

/// Context builder for ergonomic context construction
pub struct ContextBuilder {
    request_id: String,
    tenant_id: String,
    trace_id: String,
    is_turbo_mode: bool,
}

impl ContextBuilder {
    /// Create new builder
    pub fn new(request_id: impl Into<String>) -> Self {
        Self {
            request_id: request_id.into(),
            tenant_id: String::new(),
            trace_id: String::new(),
            is_turbo_mode: false,
        }
    }

    /// Set tenant ID
    pub fn tenant(mut self, tenant_id: impl Into<String>) -> Self {
        self.tenant_id = tenant_id.into();
        self
    }

    /// Set trace ID
    pub fn trace(mut self, trace_id: impl Into<String>) -> Self {
        self.trace_id = trace_id.into();
        self
    }

    /// Enable turbo mode
    pub fn turbo(mut self, enabled: bool) -> Self {
        self.is_turbo_mode = enabled;
        self
    }

    /// Build the context
    pub fn build(self) -> SovereignContext {
        let ctx = SovereignContext {
            request_id: self.request_id,
            tenant_id: self.tenant_id,
            trace_id: self.trace_id,
            is_turbo_mode: self.is_turbo_mode,
            timestamp: SovereignContext::current_timestamp(),
        };
        debug_assert!(ctx.is_valid(), "Built context must be valid");
        ctx
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sovereign_context_creation() {
        let ctx = SovereignContext::new(
            "req-123".to_string(),
            "tenant-1".to_string(),
            "trace-abc".to_string(),
        );
        assert!(ctx.is_valid());
        assert!(!ctx.is_turbo_mode);
    }

    #[test]
    fn sovereign_context_turbo() {
        let ctx = SovereignContext::new_turbo(
            "req-456".to_string(),
            "tenant-2".to_string(),
            "trace-def".to_string(),
        );
        assert!(ctx.is_turbo_mode);
    }

    #[test]
    fn context_builder_flow() {
        let ctx = ContextBuilder::new("req-789")
            .tenant("tenant-3")
            .trace("trace-xyz")
            .turbo(true)
            .build();
        assert!(ctx.is_valid());
        assert!(ctx.is_turbo_mode);
        assert_eq!(ctx.request_id, "req-789");
    }

    #[test]
    fn context_spawn_child() {
        let parent =
            SovereignContext::new("parent".to_string(), "t1".to_string(), "trace-1".to_string());
        let child = parent.spawn_child("child".to_string());
        assert_eq!(child.tenant_id, parent.tenant_id);
        assert_eq!(child.trace_id, parent.trace_id);
        assert_ne!(child.request_id, parent.request_id);
    }

    #[test]
    fn context_serialization() {
        let ctx = SovereignContext::new(
            "req-ser".to_string(),
            "tenant-ser".to_string(),
            "trace-ser".to_string(),
        );
        let json = serde_json::to_string(&ctx).expect("should serialize");
        let deserialized: SovereignContext =
            serde_json::from_str(&json).expect("should deserialize");
        assert_eq!(ctx.request_id, deserialized.request_id);
    }
}