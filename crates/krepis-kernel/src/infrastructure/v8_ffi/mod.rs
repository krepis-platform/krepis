pub mod bridge;

// FfiBuffer 구조체와 핵심 FFI 함수들을 노출
pub use bridge::{FfiBuffer, initialize_kernel, free_buffer, create_context};