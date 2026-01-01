use anyhow::Result;
use std::sync::Arc;
use tracing::{info, error};

use crate::adapters::pool::{SovereignPool};
use crate::adapters::storage::SovereignJournal;
use crate::domain::journal::{TransactionLog, LogStatus};
use crate::domain::now_ms;

/// [CQS: Command] 테넌트 스크립트 실행 명령
/// 테넌트 확인부터 실행, 저널링까지의 전체 생명주기를 원자적으로 관리합니다.
pub struct ExecuteTenantScript<'a> {
    pool: &'a SovereignPool,
    journal: &'a Arc<SovereignJournal>,
}

impl<'a> ExecuteTenantScript<'a> {
    pub fn new(pool: &'a SovereignPool, journal: &'a Arc<SovereignJournal>) -> Self {
        Self { pool, journal }
    }

    /// 실행 명령의 진입점
    pub async fn run(&self, tenant_id: &str, script: &str) -> Result<String> {
        let timestamp = now_ms();
        let request_id = uuid::Uuid::new_v4().to_string();

        // 1. [Lifecycle] 실행 시작 저널링
        self.log(tenant_id, &request_id, "execute_start", LogStatus::Started, timestamp)?;

        // 2. [Resource] Isolate 확보 (Adapter 호출)
        let mut guard = self.pool.acquire(tenant_id)?;
        let runtime = guard.runtime_mut();

        // 3. [Execution] 스크립트 실행
        info!("🚀 [Command] Executing script for tenant: {}", tenant_id);
        
        let result = match self.execute_raw(runtime, tenant_id, script).await {
            Ok(val) => {
                self.log(tenant_id, &request_id, "execute_success", LogStatus::Completed, now_ms())?;
                Ok(val)
            }
            Err(e) => {
                error!("💥 [Command] Execution failed for {}: {}", tenant_id, e);
                self.log(tenant_id, &request_id, "execute_fail", LogStatus::Failed, now_ms())?;
                Err(e)
            }
        };

        result
    }

    /// 내부 V8 실행 로직 (Hexagonal Adapter와 통신)
    async fn execute_raw(&self, runtime: &mut deno_core::JsRuntime, tenant_id: &str, script: &str) -> Result<String> {
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
    fn log(&self, tid: &str, rid: &str, op: &str, status: LogStatus, ts: i64) -> Result<()> {
        self.journal.log_transaction(&TransactionLog {
            timestamp: ts,
            op_name: format!("{}:{}", tid, op),
            request_id: rid.to_string(),
            status,
        })
    }
}