use anyhow::Result;
use std::sync::Arc;
use krepis_kernel::adapters::storage::SovereignJournal;
use krepis_kernel::adapters::pool::{SovereignPool, PoolConfig};
use krepis_kernel::kernel::ExecuteTenantScript;

fn main() -> Result<()> {
    tracing_subscriber::fmt::init();
    let rt = tokio::runtime::Builder::new_current_thread().enable_all().build()?;

    rt.block_on(async {
        let local = tokio::task::LocalSet::new();
        local.run_until(async {
            // 초기화
            let journal = Arc::new(SovereignJournal::new("./.krepis/storage")?);
            let pool = SovereignPool::new(journal.clone(), PoolConfig::default());

            // 💡 CQS 적용: 명령 객체 생성
            let cmd = ExecuteTenantScript::new(&pool, &journal);

            // 💡 실행: 이제 로직은 main이 아닌 Command 내부에 캡슐화되어 있습니다.
            let tenants = vec!["alpha", "beta"];
            for tid in tenants {
                let js_code = format!("Deno.core.ops.op_log_from_js('info', 'Hello from {}');", tid);
                cmd.run(tid, &js_code).await?;
            }

            Ok(())
        }).await
    })
}