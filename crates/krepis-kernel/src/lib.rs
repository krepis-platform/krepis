// 1. Trinity 계층 선언
pub mod domain;     // Functional Core (Pure)
pub mod adapters;   // Hexagonal Adapters (V8, Sled, Network)
pub mod infrastructure;

// 3. 편의를 위한 상위 레벨 Re-export
// adapters::storage::mod.rs가 SovereignJournal을 노출하고 있어야 합니다.
pub use adapters::storage::SovereignJournal;
pub use adapters::pool::SovereignPool;