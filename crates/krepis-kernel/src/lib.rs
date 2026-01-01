use prost::Message;
use std::slice;

pub mod proto {
    include!(concat!(env!("OUT_DIR"), "/krepis.core.rs"));
}

use proto::{InitializeRequest, InitializeResponse, KrepisContext};

#[repr(C)]
pub struct FfiBuffer {
    pub data: *mut u8,
    pub len: usize,
    pub cap: usize,
}

#[no_mangle]
pub extern "C" fn initialize_kernel(buffer_ptr: *const u8, buffer_len: usize) -> *mut FfiBuffer {
    // SAFETY: Caller must ensure buffer_ptr points to valid memory
    let buffer = unsafe { slice::from_raw_parts(buffer_ptr, buffer_len) };
    
    let response = match InitializeRequest::decode(buffer) {
        Ok(request) => {
            let ctx = request.context.unwrap_or_default();
            eprintln!("✅ Kernel initialized - RequestID: {}", ctx.request_id);
            
            InitializeResponse {
                success: true,
                error_message: String::new(),
            }
        }
        Err(e) => InitializeResponse {
            success: false,
            error_message: format!("Decode error: {}", e),
        },
    };
    
    // 1. 응답 인코딩
    let mut encoded = response.encode_to_vec();
    
    // 2. Vec의 소유권을 추출하고 해제 방지(forget)
    let data = encoded.as_mut_ptr();
    let len = encoded.len();
    let cap = encoded.capacity();
    std::mem::forget(encoded); 

    // 3. FfiBuffer 구조체에 담아 포인터 반환
    let boxed_ffi = Box::new(FfiBuffer { data, len, cap });
    Box::into_raw(boxed_ffi)
}

#[no_mangle]
pub extern "C" fn free_buffer(ptr: *mut FfiBuffer) {
    if !ptr.is_null() {
        unsafe {
            let buffer = Box::from_raw(ptr); // 구조체 해제
            let _ = Vec::from_raw_parts(buffer.data, buffer.len, buffer.cap); // 내부 데이터 해제
        }
    }
}

#[no_mangle]
pub extern "C" fn create_context(
    request_id_ptr: *const u8,
    request_id_len: usize,
    is_turbo: bool,
) -> *mut FfiBuffer {
    // SAFETY: Caller must ensure valid string pointer
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
        timestamp: std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_millis() as i64,
        metadata: Default::default(),
    };
    
    let mut encoded = ctx.encode_to_vec();

    // 1. 데이터를 힙에 고정하고 소유권을 떼어냅니다.
    let data = encoded.as_mut_ptr();
    let len = encoded.len();
    let cap = encoded.capacity();
    std::mem::forget(encoded); 

    // 2. 구조체를 만들어 구조체의 포인터를 반환합니다.
    let boxed_ffi = Box::new(FfiBuffer { data, len, cap });
    Box::into_raw(boxed_ffi)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_protobuf_roundtrip() {
        let ctx = KrepisContext {
            request_id: "test-123".to_string(),
            tenant_id: "tenant-1".to_string(),
            priority: 10,
            is_turbo_mode: true,
            trace_id: "trace-abc".to_string(),
            timestamp: 1234567890,
            metadata: Default::default(),
        };
        
        let encoded = ctx.encode_to_vec();
        let decoded = KrepisContext::decode(&encoded[..]).unwrap();
        
        assert_eq!(decoded.request_id, "test-123");
        assert_eq!(decoded.is_turbo_mode, true);
    }
}