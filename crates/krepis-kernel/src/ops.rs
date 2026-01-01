use deno_core::{op2, OpState};
use std::rc::Rc;
use std::cell::RefCell;
use tracing::warn;

/// Sovereign Stats - track JS execution metrics
#[derive(Default)]
pub struct SovereignStats {
    pub js_ops_called: u64,
    pub contexts_created: u64,
}

#[op2]
#[serde] // Vec<u8>을 JS로 넘길 때 가장 안정적인 방식
pub fn op_get_context(state: &mut OpState) -> Vec<u8> {
    let ctx = state.borrow::<Rc<Vec<u8>>>();
    ctx.as_ref().clone()
}

#[op2(fast)]
pub fn op_log_from_js(
    #[string] level: String, 
    #[string] message: String
) {
    match level.as_str() {
        "info" => tracing::info!("[JS] {}", message),
        "warn" => tracing::warn!("[JS] {}", message),
        "error" => tracing::error!("[JS] {}", message),
        _ => tracing::debug!("[JS] {}", message),
    }
}

#[op2(fast)]
pub fn op_check_permission(
    #[string] permission: String,
    #[string] path: String,
) -> bool {
    warn!("🔒 Permission check: {} for {}", permission, path);
    
    match permission.as_str() {
        "read" => path.starts_with("/tmp/krepis/"),
        "write" => false, 
        "net" => false,   
        _ => false,
    }
}

#[op2(fast)]
pub fn op_increment_stats(state: &mut OpState) {
    // OpState에서 Rc<RefCell<>> 구조를 꺼낼 때의 표준 방식
    let stats_rc = state.borrow::<Rc<RefCell<SovereignStats>>>();
    stats_rc.borrow_mut().js_ops_called += 1;
}