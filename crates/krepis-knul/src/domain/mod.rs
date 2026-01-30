//! Domain Layer
//!
//! Core domain data structures for KNUL network operations.
//! Defines types for packet handling, statistics, and trait conversions.

pub mod types;

// Re-export domain types at module level
pub use types::{PacketBuffer, QuicServerStats};