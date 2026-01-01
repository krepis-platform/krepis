use deno_core::{op2, OpState};
use std::rc::Rc;
use std::cell::RefCell;
use std::sync::Arc;
use tracing::{warn, info};

use crate::adapters::storage::SovereignJournal;
use crate::domain::journal::{LogStatus, TransactionLog};
use crate::domain::tenant::TenantMetadata;
use super::state::SovereignStats;

/// [Op] Rust에서 생성한 Protobuf Context를 JS로 전달
#[op2]
#[serde]
pub fn op_get_context(state: &mut OpState) -> Vec<u8> {
    let ctx = state.borrow::<Rc<Vec<u8>>>();
    ctx.as_ref().clone()
}

/// [Op] JS에서 Rust 로깅 시스템으로 로그 전송
#[op2(fast)]
pub fn op_log_from_js(#[string] level: String, #[string] message: String) {
    match level.as_str() {
        "info" => tracing::info!("[JS] {}", message),
        "warn" => tracing::warn!("[JS] {}", message),
        "error" => tracing::error!("[JS] {}", message),
        _ => tracing::debug!("[JS] {}", message),
    }
}

/// [Op] 경로 권한 검사 (Chroot-style 가상화)
/// 
/// # Spec-002 Compliance
/// 테넌트는 자신의 가상화된 파일시스템 경계 내에서만 접근 가능
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

/// [Op] JS ops 호출 카운터 증가 (테넌트 격리 저널링)
/// 
/// # Spec-002 Compliance: Tenant Isolation
/// 각 테넌트의 통계는 `tenant_{tenant_id}_stats` Tree에 격리 저장됩니다.
#[op2(fast)]
pub fn op_increment_stats(state: &mut OpState) {
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 1. 테넌트 메타데이터에서 tenant_id 획득 (격리 키)
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let tenant_id = {
        let tenant = state.borrow::<TenantMetadata>();
        tenant.tenant_id.clone()
    };

    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 2. In-memory 상태(State) 업데이트
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let new_count = {
        let stats = state.borrow_mut::<Rc<RefCell<SovereignStats>>>();
        let mut stats_mut = stats.borrow_mut();
        stats_mut.js_ops_called += 1;
        stats_mut.js_ops_called
    };

    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 3. 부작용(Side-effect) 처리 - 테넌트 격리 저널 호출
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let journal = state.borrow::<Arc<SovereignJournal>>();
    
    // 💡 C-001 Fix: tenant_id를 명시적으로 전달하여 격리된 Tree에 저장
    if let Err(e) = journal.increment_op_count(&tenant_id, "js_ops_called") {
        warn!("⚠️  Failed to persist op count for tenant {}: {}", tenant_id, e);
    }

    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 4. 저널 로그 기록 (테넌트 격리)
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_millis() as i64;
    
    // 💡 C-001 Fix: tenant_id를 명시적으로 전달
    let _ = journal.log_transaction(&tenant_id, &TransactionLog {
        timestamp: now,
        op_name: "op_increment_stats".to_string(),
        request_id: format!("op-{}-{}", tenant_id, new_count),
        status: LogStatus::Completed,
    });
}