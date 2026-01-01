use deno_core::{op2, OpState};
use std::rc::Rc;
use std::cell::RefCell;
use std::sync::Arc;
use tracing::{warn, info};
use crate::journal::{LogStatus, SovereignJournal, TransactionLog};

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
    // 1. 가변 빌림의 범위를 제한하여 수정을 완료하고 즉시 반납합니다.
    let new_count = {
        let stats = state.borrow_mut::<Rc<RefCell<SovereignStats>>>();
        let mut stats_mut = stats.borrow_mut();
        stats_mut.js_ops_called += 1;
        stats_mut.js_ops_called // 나중에 DB에 쓸 값을 복사해서 가지고 나옵니다.
    };

    // 2. 이제 stats에 대한 가변 빌림이 끝났으므로, state에서 journal을 안전하게 빌릴 수 있습니다.
    let journal = state.borrow::<Arc<SovereignJournal>>();

    // 3. DB 영속화 작업 (이미 state 빌림이 겹치지 않음)
    if let Err(e) = journal.increment_op_count("js_ops_called") {
        warn!("⚠️  Failed to persist op count: {}", e);
    } else {
        info!("💾 Op count persisted: {}", new_count);
    }

    // 4. 로그 기록
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_millis() as i64;

    let log = TransactionLog {
        timestamp: now,
        op_name: "op_increment_stats".to_string(),
        request_id: format!("op-{}", new_count),
        status: LogStatus::Completed,
    };

    if let Err(e) = journal.log_transaction(&log) {
        warn!("⚠️  Failed to log transaction: {}", e);
    }
}