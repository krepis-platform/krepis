use deno_core::{op2, OpState};
use std::rc::Rc;
use std::cell::RefCell;
use std::sync::Arc;
use tracing::{warn, info};

use crate::adapters::storage::SovereignJournal;
use crate::domain::journal::{LogStatus, TransactionLog};
use crate::domain::tenant::TenantMetadata; // 분리된 도메인 모델 사용
use super::state::SovereignStats;

#[op2]
#[serde]
pub fn op_get_context(state: &mut OpState) -> Vec<u8> {
    let ctx = state.borrow::<Rc<Vec<u8>>>();
    ctx.as_ref().clone()
}

#[op2(fast)]
pub fn op_log_from_js(#[string] level: String, #[string] message: String) {
    match level.as_str() {
        "info" => tracing::info!("[JS] {}", message),
        "warn" => tracing::warn!("[JS] {}", message),
        "error" => tracing::error!("[JS] {}", message),
        _ => tracing::debug!("[JS] {}", message),
    }
}

#[op2(fast)]
pub fn op_check_permission(state: &mut OpState, #[string] _action: &str, #[string] path: &str) -> bool {
    // 1. 도메인 모델(Core) 획득
    let tenant = state.borrow::<TenantMetadata>();
    
    // 2. 도메인 로직(Core)에 결정을 위임 - 순수 함수 호출
    let physical_path = tenant.safe_remap(path);
    let is_allowed = tenant.is_path_allowed(&physical_path);
    
    info!("[{}] Path Check: {} -> {}", 
        tenant.tenant_id, path, if is_allowed { "ALLOWED" } else { "DENIED" });
        
    is_allowed
}

#[op2(fast)]
pub fn op_increment_stats(state: &mut OpState) {
    // 1. 상태(State) 업데이트
    let new_count = {
        let stats = state.borrow_mut::<Rc<RefCell<SovereignStats>>>();
        let mut stats_mut = stats.borrow_mut();
        stats_mut.js_ops_called += 1;
        stats_mut.js_ops_called
    };

    // 2. 부작용(Side-effect) 처리 - Adapter 호출
    let journal = state.borrow::<Arc<SovereignJournal>>();
    
    if let Err(e) = journal.increment_op_count("js_ops_called") {
        warn!("⚠️  Failed to persist op count: {}", e);
    }

    // 3. 저널 로그 기록
    let now = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_millis() as i64;
    let _ = journal.log_transaction(&TransactionLog {
        timestamp: now,
        op_name: "op_increment_stats".to_string(),
        request_id: format!("op-{}", new_count),
        status: LogStatus::Completed,
    });
}