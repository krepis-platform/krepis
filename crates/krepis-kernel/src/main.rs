use anyhow::Result;
use deno_core::{JsRuntime, RuntimeOptions, PollEventLoopOptions};
use prost::Message;
use std::rc::Rc;
use std::cell::RefCell;
use tracing::{info};

mod proto {
    include!(concat!(env!("OUT_DIR"), "/krepis.core.rs"));
}

mod ops;

use proto::KrepisContext;
use ops::SovereignStats;

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
    tracing_subscriber::fmt::init();

    info!("🚀 Krepis Sovereign Kernel Host v2.0.0");
    info!("⚡ Initializing Rust Control Plane...");

    let ctx = create_sovereign_context();
    let ctx_serialized = ctx.encode_to_vec();
    
    info!("✅ Context created: RequestID={}", ctx.request_id);

    let mut runtime = create_sovereign_runtime(ctx_serialized)?;
    info!("🎯 Deno Isolate spawned - Rust maintains sovereignty");
    
    let js_code = r#"
        (async () => {
            console.log("🔷 JavaScript Execution Plane Active");
            
            Deno.core.ops.op_log_from_js("info", "JS Runtime initialized");
            
            const ctxBuffer = Deno.core.ops.op_get_context();
            console.log("📦 Context received from Rust:", ctxBuffer.byteLength, "bytes");
            
            Deno.core.ops.op_increment_stats();
            
            const canRead = Deno.core.ops.op_check_permission("read", "/tmp/krepis/test");
            console.log("🔒 Read permission:", canRead);
            
            return "OK";
        })();
    "#;

    runtime.execute_script("[krepis:bootstrap]", js_code.to_string())?;
    
    // v0.316 대응: PollEventLoopOptions 구조체 사용
    runtime.run_event_loop(PollEventLoopOptions {
        wait_for_inspector: false,
        pump_v8_message_loop: true,
    }).await?;

    // 실행 후 통계 확인
    let stats_rc = runtime.op_state().borrow().borrow::<Rc<RefCell<SovereignStats>>>().clone();
    info!("📊 JS Ops Called: {}", stats_rc.borrow().js_ops_called);
    info!("🎉 Sovereign Kernel Host operational");

    Ok(())
}

fn create_sovereign_context() -> KrepisContext {
    KrepisContext {
        request_id: uuid::Uuid::new_v4().to_string(),
        tenant_id: "sovereign-tenant".to_string(),
        priority: 10,
        is_turbo_mode: true,
        trace_id: uuid::Uuid::new_v4().to_string(),
        timestamp: std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_millis() as i64,
        metadata: Default::default(),
    }
}

fn create_sovereign_runtime(ctx_buffer: Vec<u8>) -> Result<JsRuntime> {
    let ctx_buffer = Rc::new(ctx_buffer);
    let stats = Rc::new(RefCell::new(SovereignStats::default()));

    let mut krepis_ext = krepis_core::init_ops();

    krepis_ext.op_state_fn = Some(Box::new(move |state: &mut deno_core::OpState| {
        state.put(ctx_buffer.clone());
        state.put(stats.clone());
    }));

    let runtime = JsRuntime::new(RuntimeOptions {
        extensions: vec![krepis_ext],
        ..Default::default()
    });

    Ok(runtime)
}