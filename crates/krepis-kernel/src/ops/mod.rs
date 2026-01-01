pub mod bridge;
pub mod state;

pub use state::SovereignStats;

deno_core::extension!(
    krepis_sovereign,
    ops = [
        bridge::op_get_context,
        bridge::op_log_from_js,
        bridge::op_check_permission,
        bridge::op_increment_stats,
    ],
);