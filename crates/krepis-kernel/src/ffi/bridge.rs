use prost::Message;
use std::slice;
use crate::proto::{InitializeRequest, InitializeResponse, KrepisContext};
use crate::domain::now_ms;

/// [FFI Adapter] C-Compatible Buffer Management
#[repr(C)]
pub struct FfiBuffer {
    pub data: *mut u8,
    pub len: usize,
    pub cap: usize,
}

impl FfiBuffer {
    /// Vec을 FfiBuffer 포인터로 전환 (Ownership Transfer)
    pub fn from_vec(mut v: Vec<u8>) -> *mut Self {
        let data = v.as_mut_ptr();
        let len = v.len();
        let cap = v.capacity();
        std::mem::forget(v);
        Box::into_raw(Box::new(FfiBuffer { data, len, cap }))
    }
}

#[no_mangle]
pub extern "C" fn initialize_kernel(buffer_ptr: *const u8, buffer_len: usize) -> *mut FfiBuffer {
    let buffer = unsafe { slice::from_raw_parts(buffer_ptr, buffer_len) };
    
    let response = match InitializeRequest::decode(buffer) {
        Ok(request) => {
            let ctx = request.context.unwrap_or_default();
            eprintln!("✅ Kernel initialized - RequestID: {}", ctx.request_id);
            InitializeResponse { success: true, error_message: String::new() }
        }
        Err(e) => InitializeResponse { success: false, error_message: format!("Decode error: {}", e) },
    };
    
    FfiBuffer::from_vec(response.encode_to_vec())
}

#[no_mangle]
pub extern "C" fn create_context(
    request_id_ptr: *const u8,
    request_id_len: usize,
    is_turbo: bool,
) -> *mut FfiBuffer {
    let request_id = unsafe {
        let slice = slice::from_raw_parts(request_id_ptr, request_id_len);
        String::from_utf8_lossy(slice).to_string()
    };
    
    let ctx = KrepisContext {
        request_id,
        tenant_id: String::from("default"),
        priority: if is_turbo { 10 } else { 5 },
        is_turbo_mode: is_turbo,
        trace_id: uuid::Uuid::new_v4().to_string(),
        timestamp: now_ms(),
        metadata: Default::default(),
    };
    
    FfiBuffer::from_vec(ctx.encode_to_vec())
}

#[no_mangle]
pub extern "C" fn free_buffer(ptr: *mut FfiBuffer) {
    if !ptr.is_null() {
        unsafe {
            let buffer = Box::from_raw(ptr);
            let _ = Vec::from_raw_parts(buffer.data, buffer.len, buffer.cap);
        }
    }
}