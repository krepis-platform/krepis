// build.rs가 생성한 krepis.core.rs 파일을 이 위치에 포함시킵니다.
pub mod core {
    include!(concat!(env!("OUT_DIR"), "/krepis.core.rs"));
}

// 외부에서 사용하기 편하도록 주요 타입들을 re-export 합니다.
pub use core::*;