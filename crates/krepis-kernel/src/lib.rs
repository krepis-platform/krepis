// 1. Trinity 계층 선언
pub mod domain;     // Functional Core (Pure)
pub mod adapters;   // Hexagonal Adapters (V8, Sled, Network)
pub mod kernel;     // CQS (Commands, Queries)
pub mod ops;        // Deno Bridge
pub mod ffi;        // External C-FFI Bridge

// 2. Protobuf 스키마 (Shared Contract) 
// 단 한 번만 선언해야 합니다.
pub mod proto {
    // build.rs에 의해 생성된 파일을 포함합니다.
    include!(concat!(env!("OUT_DIR"), "/krepis.core.rs"));
}

// 3. 편의를 위한 상위 레벨 Re-export
// adapters::storage::mod.rs가 SovereignJournal을 노출하고 있어야 합니다.
pub use adapters::storage::SovereignJournal;
pub use adapters::pool::SovereignPool;