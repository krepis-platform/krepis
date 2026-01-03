use prost::Message;
use std::slice;
use crate::proto::{InitializeRequest, InitializeResponse, KrepisContext, FfiResponse, ffi_response};
use crate::domain::now_ms;
use crate::domain::tenant::TenantError;

#[repr(C)]
pub struct FfiBuffer {
    pub data: *mut u8,
    pub len: usize,
    pub cap: usize,
}

impl FfiBuffer {
    pub fn from_vec(mut v: Vec<u8>) -> *mut Self {
        let data = v.as_mut_ptr();
        let len = v.len();
        let cap = v.capacity();
        std::mem::forget(v);
        Box::into_raw(Box::new(FfiBuffer { data, len, cap }))
    }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [Helper] FfiResponse Factory
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
impl FfiResponse {
    /// 성공 응답 생성 헬퍼
    fn success(payload: Vec<u8>, request_id: String) -> Self {
        Self {
            result: Some(ffi_response::Result::SuccessPayload(payload)),
            request_id,
            trace_id: uuid::Uuid::new_v4().to_string(), // 실제 구현시 Context에서 가져옴
            protocol_version: 1,
            ..Default::default()
        }
    }

    /// 에러 응답 생성 헬퍼 (TenantError -> Protobuf Error 변환 포함)
    fn error(err: TenantError, request_id: String, trace_id: String) -> Self {
        Self {
            result: Some(ffi_response::Result::Error(err.into_proto(request_id.clone(), trace_id.clone()))),
            request_id,
            trace_id,
            protocol_version: 1,
            ..Default::default()
        }
    }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [FFI Exports]
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

#[no_mangle]
pub extern "C" fn initialize_kernel(buffer_ptr: *const u8, buffer_len: usize) -> *mut FfiBuffer {
    let buffer = unsafe { slice::from_raw_parts(buffer_ptr, buffer_len) };
    let request_id = "init".to_string();
    
    let envelope = match InitializeRequest::decode(buffer) {
        Ok(request) => {
            let ctx = request.context.unwrap_or_default();
            eprintln!("✅ Kernel initialized - RequestID: {}", ctx.request_id);
            let resp = InitializeResponse { success: true, error_message: String::new() };
            FfiResponse::success(resp.encode_to_vec(), ctx.request_id)
        }
        Err(e) => {
            // 디코드 실패는 시스템 내부 에러로 처리
            FfiResponse::error(
                TenantError::Internal(format!("Decode error: {}", e)),
                request_id,
                "system".to_string()
            )
        }
    };
    
    FfiBuffer::from_vec(envelope.encode_to_vec())
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
        request_id: request_id.clone(),
        tenant_id: String::from("default"),
        priority: if is_turbo { 10 } else { 5 },
        is_turbo_mode: is_turbo,
        trace_id: uuid::Uuid::new_v4().to_string(),
        timestamp: now_ms(),
        metadata: Default::default(),
    };

    let envelope = FfiResponse::success(ctx.encode_to_vec(), request_id);
    FfiBuffer::from_vec(envelope.encode_to_vec())
}

/// [중요] 모든 FfiBuffer 해제 단일화
#[no_mangle]
pub extern "C" fn free_buffer(ptr: *mut FfiBuffer) {
    if !ptr.is_null() {
        unsafe {
            let buffer = Box::from_raw(ptr);
            let _ = Vec::from_raw_parts(buffer.data, buffer.len, buffer.cap);
        }
    }
}
