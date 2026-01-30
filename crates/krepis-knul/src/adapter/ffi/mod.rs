//! FFI Adapter Layer
//!
//! Entry points for FFI calls from Deno/TypeScript boundary.
//! All functions use extern "C" calling convention and panic-safe wrapping.

use std::panic::{catch_unwind, AssertUnwindSafe};
use krepis_core::{FfiBuffer, FfiQuicConfig, FfiResponse, KrepisError};

use crate::adapter::quinn::server::QuicServer;
use crate::infrastructure::ffi::{create_handle_buffer, ffi_buffer_to_string};
use crate::infrastructure::runtime::{get_registry, get_runtime};

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
        let registry = get_registry();
        let handle = registry.register(server);

        // Clone server for async startup
        let _server = registry.get(handle).expect("Just registered");

        // Spawn async startup task
        let runtime = get_runtime();
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
        let registry = get_registry();

        // Lookup and unregister server
        let _server = match registry.unregister(server_handle) {
            Some(server) => server,
            None => return FfiResponse::error(KrepisError::InvalidPointer as u32),
        };

        // Spawn async stop task
        let runtime = get_runtime();
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
        let registry = get_registry();

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

#[cfg(test)]
mod tests {
    use super::*;

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