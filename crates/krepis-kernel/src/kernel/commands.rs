use anyhow::Result;
use std::sync::Arc;
use tracing::{info, error};

use crate::adapters::pool::SovereignPool;
use crate::adapters::storage::SovereignJournal;
use crate::domain::journal::{TransactionLog, LogStatus};
use crate::domain::now_ms;

/// [CQS: Command] 테넌트 스크립트 실행 명령
/// 
/// 테넌트 확인부터 실행, 저널링까지의 전체 생명주기를 원자적으로 관리합니다.
/// 
/// # Spec-002 Compliance: Tenant Isolation
/// 모든 저널 기록은 테넌트별로 격리된 Sled Tree에 저장됩니다.
pub struct ExecuteTenantScript<'a> {
    pool: &'a SovereignPool,
    journal: &'a Arc<SovereignJournal>,
}

impl<'a> ExecuteTenantScript<'a> {
    pub fn new(pool: &'a SovereignPool, journal: &'a Arc<SovereignJournal>) -> Self {
        Self { pool, journal }
    }

    /// 실행 명령의 진입점
    /// 
    /// # Arguments
    /// * `tenant_id` - 실행할 테넌트의 식별자 (격리 키로 사용)
    /// * `script` - 실행할 JavaScript 코드
    pub async fn run(&self, tenant_id: &str, script: &str) -> Result<String> {
        let timestamp = now_ms();
        let request_id = uuid::Uuid::new_v4().to_string();

        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        // 1. [Lifecycle] 실행 시작 저널링 (테넌트 격리)
        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        self.log(tenant_id, &request_id, "execute_start", LogStatus::Started, timestamp)?;

        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        // 2. [Resource] Isolate 확보 (Adapter 호출)
        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        let mut guard = self.pool.acquire(tenant_id)?;
        let runtime = guard.runtime_mut();

        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        // 3. [Execution] 스크립트 실행
        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        info!("🚀 [Command] Executing script for tenant: {}", tenant_id);
        
        let result = match self.execute_raw(runtime, tenant_id, script).await {
            Ok(val) => {
                // 💡 C-001 Fix: tenant_id 전달하여 격리된 Tree에 저장
                self.log(tenant_id, &request_id, "execute_success", LogStatus::Completed, now_ms())?;
                Ok(val)
            }
            Err(e) => {
                error!("💥 [Command] Execution failed for {}: {}", tenant_id, e);
                // 💡 C-001 Fix: tenant_id 전달하여 격리된 Tree에 저장
                self.log(tenant_id, &request_id, "execute_fail", LogStatus::Failed, now_ms())?;
                Err(e)
            }
        };

        result
    }

    /// 내부 V8 실행 로직 (Hexagonal Adapter와 통신)
    async fn execute_raw(
        &self, 
        runtime: &mut deno_core::JsRuntime, 
        tenant_id: &str, 
        script: &str
    ) -> Result<String> {
        let specifier = Box::leak(format!("[{}:bootstrap]", tenant_id).into_boxed_str());
        runtime.execute_script(specifier, script.to_string())?;
        
        // 이벤트 루프 완료 대기
        runtime.run_event_loop(deno_core::PollEventLoopOptions {
            wait_for_inspector: false,
            pump_v8_message_loop: true,
        }).await?;

        Ok("Execution Success".to_string())
    }

    /// 저널 기록 도우미
    /// 
    /// # Arguments
    /// * `tenant_id` - 테넌트 식별자 (격리 키)
    /// * `request_id` - 요청 ID
    /// * `op` - 오퍼레이션 이름
    /// * `status` - 로그 상태
    /// * `ts` - 타임스탬프
    fn log(
        &self, 
        tenant_id: &str, 
        request_id: &str, 
        op: &str, 
        status: LogStatus, 
        ts: i64
    ) -> Result<()> {
        // 💡 C-001 Fix: tenant_id를 첫 번째 인자로 전달
        self.journal.log_transaction(tenant_id, &TransactionLog {
            timestamp: ts,
            op_name: format!("{}:{}", tenant_id, op),
            request_id: request_id.to_string(),
            status,
        })
    }
}