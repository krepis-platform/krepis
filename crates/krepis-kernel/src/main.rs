use anyhow::Result;
use deno_core::{JsRuntime, RuntimeOptions, PollEventLoopOptions};
use prost::Message;
use std::rc::Rc;
use std::cell::RefCell;
use std::sync::Arc;
use tracing::{info, error};

mod proto {
    include!(concat!(env!("OUT_DIR"), "/krepis.core.rs"));
}

mod ops;
mod journal; // 모듈명을 journal로 통일

use proto::KrepisContext;
use ops::SovereignStats;
use journal::{SovereignJournal, TransactionLog, LogStatus};

// v0.316 전용 extension 매크로 선언
deno_core::extension!(
    krepis_core,
    ops = [
        ops::op_get_context,
        ops::op_log_from_js,
        ops::op_check_permission,
        ops::op_increment_stats,
    ],
);

#[tokio::main]
async fn main() -> Result<()> {
    // 1. 시스템 초기화
    tracing_subscriber::fmt::init();
    info!("🚀 Krepis Sovereign Kernel Host v2.0.0");
    info!("⚡ Initializing Rust Control Plane...");

    // 2. Sovereign Journal (Sled DB) 초기화
    let journal_path = "./.krepis/storage";
    std::fs::create_dir_all(journal_path)?;
    let journal = Arc::new(SovereignJournal::new(journal_path)?);

    // 3. Recovery: Sled DB로부터 기존 통계 복구
    let recovered_ops = journal.recover_op_count("js_ops_called")?;
    info!("🔄 Recovery complete: {} ops restored from storage", recovered_ops);

    // 4. Sovereign Context 생성
    let ctx = create_sovereign_context();
    let ctx_serialized = ctx.encode_to_vec();
    
    info!("✅ Context created: RequestID={}", ctx.request_id);
    info!("🔒 Turbo Mode: {}", ctx.is_turbo_mode);
    info!("📊 Priority Level: {}", ctx.priority);

    // 5. 커널 시작 로그 기록 (Journaling)
    journal.log_transaction(&TransactionLog {
        timestamp: ctx.timestamp,
        op_name: "kernel_init".to_string(),
        request_id: ctx.request_id.clone(),
        status: LogStatus::Started,
    })?;

    // 6. 런타임 생성 (복구된 통계와 저널 주입)
    let mut runtime = create_sovereign_runtime(
        ctx_serialized,
        journal.clone(),
        recovered_ops,
    )?;
    info!("🎯 Deno Isolate spawned - Rust maintains sovereignty");
    
    // 7. JavaScript 실행 코드
    let js_code = r#"
        (async () => {
            console.log("🔷 JavaScript Execution Plane Active");
            
            Deno.core.ops.op_log_from_js("info", "JS Runtime initialized");
            
            const ctxBuffer = Deno.core.ops.op_get_context();
            console.log("📦 Context received from Rust:", ctxBuffer.byteLength, "bytes");
            
            // 통계 증가 (이제 DB에도 동기화됨)
            Deno.core.ops.op_increment_stats();
            Deno.core.ops.op_increment_stats();
            
            const canRead = Deno.core.ops.op_check_permission("read", "/tmp/krepis/test");
            console.log("🔒 Read permission:", canRead);
            
            return "OK";
        })();
    "#;

    match runtime.execute_script("[krepis:bootstrap]", js_code.to_string()) {
        Ok(_) => {
            info!("✅ JavaScript bootstrap executed");
            
            // v0.316 규격 이벤트 루프 실행
            runtime.run_event_loop(PollEventLoopOptions {
                wait_for_inspector: false,
                pump_v8_message_loop: true,
            }).await?;
            
            // 실행 후 최종 통계 확인
            let stats_rc = runtime.op_state().borrow().borrow::<Rc<RefCell<SovereignStats>>>().clone();
            info!("📊 Total JS Ops Called: {} (Recovered: {})", 
                stats_rc.borrow().js_ops_called, recovered_ops);

            // 커널 정상 종료 로그 기록
            journal.log_transaction(&TransactionLog {
                timestamp: now_ms(),
                op_name: "kernel_shutdown".to_string(),
                request_id: ctx.request_id.clone(),
                status: LogStatus::Completed,
            })?;
            
            info!("📚 Journal entries: {}", journal.journal_count());
            info!("🎉 Sovereign Kernel Host operational");
        }
        Err(e) => {
            error!("❌ JavaScript execution failed: {}", e);
            journal.log_transaction(&TransactionLog {
                timestamp: now_ms(),
                op_name: "kernel_error".to_string(),
                request_id: ctx.request_id.clone(),
                status: LogStatus::Failed,
            })?;
        }
    }

    Ok(())
}

fn create_sovereign_context() -> KrepisContext {
    KrepisContext {
        request_id: uuid::Uuid::new_v4().to_string(),
        tenant_id: "sovereign-tenant".to_string(),
        priority: 10,
        is_turbo_mode: true,
        trace_id: uuid::Uuid::new_v4().to_string(),
        timestamp: now_ms(),
        metadata: Default::default(),
    }
}

fn create_sovereign_runtime(
    ctx_buffer: Vec<u8>,
    journal: Arc<SovereignJournal>,
    recovered_ops: u64,
) -> Result<JsRuntime> {
    let ctx_buffer = Rc::new(ctx_buffer);
    
    // 복구된 값으로 stats 초기화
    let stats = Rc::new(RefCell::new(SovereignStats {
        js_ops_called: recovered_ops,
        contexts_created: 0,
    }));

    let mut krepis_ext = krepis_core::init_ops();

    // v0.316 규격에 따른 state 주입 (journal 추가)
    krepis_ext.op_state_fn = Some(Box::new(move |state: &mut deno_core::OpState| {
        state.put(ctx_buffer.clone());
        state.put(stats.clone());
        state.put(journal.clone());
    }));

    let runtime = JsRuntime::new(RuntimeOptions {
        extensions: vec![krepis_ext],
        ..Default::default()
    });

    Ok(runtime)
}

fn now_ms() -> i64 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_millis() as i64
}