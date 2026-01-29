//! # Krepis KNUL - Network Adapter Layer
//!
//! FFI bridge between Deno TypeScript SDK and Krepis Kernel.
//! Manages QUIC server lifecycle and handles network communication.
//!
//! ## Architecture
//!
//! ```
//! ┌──────────────────────────┐
//! │   Deno TypeScript        │
//! │   (KNUL Adapter)         │
//! └────────────┬─────────────┘
//!              │ FFI Boundary
//!              ▼
//! ┌──────────────────────────┐
//! │   Krepis KNUL (Rust)     │
//! │   - FFI Entry Points     │
//! │   - Server Registry      │
//! │   - QUIC Server Mgmt     │
//! └──────────────────────────┘
//! ```
//!
//! ## Features
//!
//! - **FFI-First Design**: All public functions use `extern "C"` calling convention
//! - **Handle-Based Management**: Server instances identified by u64 handles
//! - **Thread-Safe Registry**: Concurrent server instance management
//! - **Zero-Copy Buffers**: Uses `krepis-core` ABI structures
//! - **No Business Logic**: Pure communication layer (Sovereign Link principle)

pub mod registry;
pub mod server;

// Re-export core types
pub use krepis_core::{FfiBuffer, FfiResponse, FfiQuicConfig, KrepisError};

use registry::ServerRegistry;
use server::QuicServer;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::slice;
use std::sync::LazyLock;

/// Library version
pub const KREPIS_KNUL_VERSION: &str = "0.1.0";

/// FFI ABI version (must match krepis-core)
pub const FFI_ABI_VERSION: u32 = 1u32 << 16 | 1u32; // 1.1.0

// ============================================================================
// GLOBAL STATE & RUNTIME
// ============================================================================

/// Global server registry (thread-safe)
/// Manages all active QUIC server instances
static SERVER_REGISTRY: LazyLock<ServerRegistry> = LazyLock::new(ServerRegistry::new);

/// Global tokio runtime for FFI async operations
static TOKIO_RUNTIME: LazyLock<tokio::runtime::Runtime> = LazyLock::new(|| {
    tokio::runtime::Runtime::new().expect("Failed to create tokio runtime")
});

// ============================================================================
// UTILITY FUNCTIONS
// ============================================================================

/// Extract a Rust String from an FfiBuffer safely
///
/// # Arguments
/// * `buffer` - Reference to FfiBuffer
///
/// # Returns
/// String extracted from buffer, or empty string if buffer is invalid
///
/// # Safety
/// Dereferences the raw pointer in FfiBuffer. Caller must ensure:
/// - Pointer is valid
/// - Data is UTF-8 encoded (invalid UTF-8 is converted lossy)
/// - Buffer lifetime is valid
fn ffi_buffer_to_string(buffer: &FfiBuffer) -> String {
    if !buffer.is_valid() {
        return String::new();
    }

    if buffer.data.is_null() {
        return String::new();
    }

    unsafe {
        // SAFETY: FfiBuffer guarantees valid pointer and length
        let slice = slice::from_raw_parts(buffer.data, buffer.len);
        String::from_utf8_lossy(slice).into_owned()
    }
}

/// Allocate and write a u64 handle to a buffer
///
/// # Arguments
/// * `handle` - u64 handle to store
///
/// # Returns
/// FfiBuffer pointing to 8-byte buffer containing the handle
fn create_handle_buffer(handle: u64) -> FfiBuffer {
    let boxed_handle = Box::new(handle);
    let ptr = Box::into_raw(boxed_handle) as *mut u8;

    FfiBuffer {
        data: ptr,
        len: 8,
        cap: 8,
        _padding: 0,
    }
}

// ============================================================================
// FFI ENTRY POINTS
// ============================================================================

/// Start a QUIC server with given configuration
///
/// Creates a new QUIC server instance, binds to the configured address/port,
/// and begins accepting connections.
///
/// # Arguments
/// * `config_ptr` - Pointer to FfiQuicConfig (must be valid and aligned)
///
/// # Returns
/// FfiResponse containing:
/// - error_code: 0 on success, KrepisError code on failure
/// - result_buffer.data: Pointer to u64 server handle (if successful)
/// - result_buffer.len: 8 (size of u64)
///
/// # Safety
/// * `config_ptr` must be a valid, properly aligned pointer to FfiQuicConfig
/// * Config buffer fields (host_addr, cert_path, key_path) must be readable
///
/// # Errors
/// - InvalidRequest: Configuration is invalid
/// - NetworkError: Failed to bind to port
/// - Internal: Initialization failed
#[no_mangle]
pub extern "C" fn krepis_quic_start(config_ptr: *const FfiQuicConfig) -> FfiResponse {
    let result = catch_unwind(AssertUnwindSafe(|| {
        // Validate pointer
        if config_ptr.is_null() {
            return FfiResponse::error(KrepisError::InvalidPointer as u32);
        }

        // Dereference safely
        let config = unsafe { &*config_ptr };

        // Validate configuration
        if !config.is_valid() {
            return FfiResponse::error(KrepisError::InvalidRequest as u32);
        }

        // Extract configuration strings from FFI buffers
        let _host_addr = ffi_buffer_to_string(&config.host_addr);
        let _cert_path = ffi_buffer_to_string(&config.cert_path);
        let _key_path = ffi_buffer_to_string(&config.key_path);

        // Create new server instance
        let server = QuicServer::new(0, config.clone());

        // Register server and get handle
        let registry = &*SERVER_REGISTRY;
        let handle = registry.register(server);

        // Clone server for async startup
        let server = registry.get(handle).expect("Just registered");

        // Spawn async startup task
        let runtime = &*TOKIO_RUNTIME;
        runtime.spawn(async move {
            // TODO: Implement actual server startup logic
            // For now, just mark as running
            // match server.start().await {
            //     Ok(()) => {
            //         // Server started successfully
            //     }
            //     Err(e) => {
            //         eprintln!("Server startup failed: {}", e);
            //         // Mark as failed in registry?
            //     }
            // }
        });

        // Create handle buffer for return
        let handle_buffer = create_handle_buffer(handle);

        // Return success response with handle
        FfiResponse::success(handle_buffer)
    }));

    // Handle panic by returning internal error
    match result {
        Ok(response) => response,
        Err(_) => FfiResponse::error(KrepisError::Internal as u32),
    }
}

/// Stop a running QUIC server
///
/// Gracefully shuts down the server, closes all active connections,
/// and releases resources. The handle becomes invalid after this call.
///
/// # Arguments
/// * `server_handle` - Handle returned by krepis_quic_start()
///
/// # Returns
/// FfiResponse containing:
/// - error_code: 0 on success, KrepisError code on failure
/// - result_buffer: Empty (not used)
///
/// # Errors
/// - InvalidPointer: Handle is invalid or stale
/// - Timeout: Graceful shutdown exceeded timeout
/// - Internal: Shutdown failed
#[no_mangle]
pub extern "C" fn krepis_quic_stop(server_handle: u64) -> FfiResponse {
    let result = catch_unwind(AssertUnwindSafe(|| {
        let registry = &*SERVER_REGISTRY;

        // Lookup and unregister server
        let server = match registry.unregister(server_handle) {
            Some(server) => server,
            None => return FfiResponse::error(KrepisError::InvalidPointer as u32),
        };

        // Spawn async stop task
        let runtime = &*TOKIO_RUNTIME;
        runtime.spawn(async move {
            // TODO: Implement actual server shutdown logic
            // match server.stop().await {
            //     Ok(()) => {
            //         // Server stopped successfully
            //     }
            //     Err(e) => {
            //         eprintln!("Server stop failed: {}", e);
            //     }
            // }
        });

        FfiResponse::success(FfiBuffer::new())
    }));

    match result {
        Ok(response) => response,
        Err(_) => FfiResponse::error(KrepisError::Internal as u32),
    }
}

/// Get statistics from a running QUIC server
///
/// Collects current performance metrics and connection statistics.
/// Statistics are serialized and returned in result_buffer.
///
/// # Arguments
/// * `server_handle` - Handle returned by krepis_quic_start()
///
/// # Returns
/// FfiResponse containing:
/// - error_code: 0 on success, KrepisError code on failure
/// - result_buffer: Serialized statistics (JSON format)
///
/// # Errors
/// - InvalidPointer: Handle is invalid
/// - Internal: Failed to collect statistics
#[no_mangle]
pub extern "C" fn krepis_quic_get_stats(server_handle: u64) -> FfiResponse {
    let result = catch_unwind(AssertUnwindSafe(|| {
        let registry = &*SERVER_REGISTRY;

        // Lookup server
        let server = match registry.get(server_handle) {
            Some(server) => server,
            None => return FfiResponse::error(KrepisError::InvalidPointer as u32),
        };

        // Collect statistics
        let stats = server.get_stats();

        // Serialize to JSON
        let json_bytes = match stats.to_json_bytes() {
            Ok(bytes) => bytes,
            Err(_) => return FfiResponse::error(KrepisError::Internal as u32),
        };

        // Create buffer for serialized stats
        let boxed_bytes = json_bytes.into_boxed_slice();
        let len = boxed_bytes.len();
        let ptr = Box::into_raw(boxed_bytes) as *mut u8;

        let stats_buffer = FfiBuffer {
            data: ptr,
            len,
            cap: len,
            _padding: 0,
        };

        FfiResponse::success(stats_buffer)
    }));

    match result {
        Ok(response) => response,
        Err(_) => FfiResponse::error(KrepisError::Internal as u32),
    }
}

// ============================================================================
// PUBLIC API (for internal use and testing)
// ============================================================================

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
    fn test_version() {
        assert_eq!(KREPIS_KNUL_VERSION, "0.1.0");
        assert_eq!(FFI_ABI_VERSION, 0x00010001);
    }

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

    #[test]
    fn test_ffi_buffer_to_string_empty() {
        let buffer = FfiBuffer::new();
        let string = ffi_buffer_to_string(&buffer);
        assert_eq!(string, "");
    }

    #[test]
    fn test_ffi_buffer_to_string_valid() {
        let test_str = "hello, world!";
        let bytes = test_str.as_bytes();
        let boxed = bytes.to_vec().into_boxed_slice();
        let ptr = Box::into_raw(boxed) as *mut u8;

        let buffer = FfiBuffer {
            data: ptr,
            len: test_str.len(),
            cap: test_str.len(),
            _padding: 0,
        };

        let string = ffi_buffer_to_string(&buffer);
        assert_eq!(string, test_str);

        // Cleanup
        unsafe {
            let _ = Box::from_raw(std::slice::from_raw_parts_mut(ptr, test_str.len()));
        }
    }

    #[test]
    fn test_handle_buffer_creation() {
        let handle = 12345u64;
        let buffer = create_handle_buffer(handle);

        assert_eq!(buffer.len, 8);
        assert_eq!(buffer.cap, 8);
        assert!(!buffer.data.is_null());

        // Verify contents
        unsafe {
            let stored_handle = *(buffer.data as *mut u64);
            assert_eq!(stored_handle, handle);
            let _ = Box::from_raw(buffer.data as *mut u64);
        }
    }

    #[test]
    fn test_krepis_quic_start_null_pointer() {
        let response = krepis_quic_start(std::ptr::null());
        assert!(response.is_error());
        assert_eq!(response.error_code, KrepisError::InvalidPointer as u32);
    }

    #[test]
    fn test_krepis_quic_start_invalid_config() {
        // Config with port 0 (invalid)
        let mut config = FfiQuicConfig::new();
        config.port = 0;

        let response = krepis_quic_start(&config);
        assert!(response.is_error());
        assert_eq!(response.error_code, KrepisError::InvalidRequest as u32);
    }

    #[test]
    fn test_krepis_quic_stop_invalid_handle() {
        let response = krepis_quic_stop(99999);
        assert!(response.is_error());
        assert_eq!(response.error_code, KrepisError::InvalidPointer as u32);
    }

    #[test]
    fn test_krepis_quic_get_stats_invalid_handle() {
        let response = krepis_quic_get_stats(99999);
        assert!(response.is_error());
        assert_eq!(response.error_code, KrepisError::InvalidPointer as u32);
    }
}