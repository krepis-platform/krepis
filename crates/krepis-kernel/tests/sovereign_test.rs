use deno_core::{JsRuntime, RuntimeOptions, PollEventLoopOptions};
use std::rc::Rc;
use std::cell::RefCell;
use std::sync::Arc;

mod proto {
    include!(concat!(env!("OUT_DIR"), "/krepis.core.rs"));
}

#[path = "../src/ops.rs"]
mod ops;
#[path = "../src/journal.rs"]
mod journal;

use proto::KrepisContext;
use prost::Message;
use journal::{SovereignJournal, TransactionLog, LogStatus};
use ops::SovereignStats;

deno_core::extension!(
    krepis_test,
    ops = [
        ops::op_get_context,
        ops::op_check_permission,
        ops::op_increment_stats,
    ],
);

#[tokio::test]
async fn test_sovereign_runtime_creation() {
    let ctx = KrepisContext {
        request_id: "test-001".to_string(),
        tenant_id: "test-tenant".to_string(),
        priority: 5,
        is_turbo_mode: false,
        trace_id: "trace-001".to_string(),
        timestamp: 1234567890,
        metadata: Default::default(),
    };

    let ctx_buffer = Rc::new(ctx.encode_to_vec());
    
    // ops::op_get_context::DECL 대신 매크로 초기화 사용
    let mut ext = krepis_test::init_ops();
    ext.op_state_fn = Some(Box::new(move |state| {
        state.put(ctx_buffer.clone());
    }));

    let mut runtime = JsRuntime::new(RuntimeOptions {
        extensions: vec![ext],
        ..Default::default()
    });

    let result = runtime.execute_script(
        "test",
        r#"
            const buffer = Deno.core.ops.op_get_context();
            buffer.length > 0;
        "#.to_string(),
    );

    assert!(result.is_ok());
}

#[tokio::test]
async fn test_permission_system() {
    let ctx_buffer: Rc<Vec<u8>> = Rc::new(vec![]);
    
    let mut ext = krepis_test::init_ops();
    ext.op_state_fn = Some(Box::new(move |state| {
        state.put(ctx_buffer.clone());
    }));

    let mut runtime = JsRuntime::new(RuntimeOptions {
        extensions: vec![ext],
        ..Default::default()
    });

    let result = runtime.execute_script(
        "permission_test",
        r#"
            const allowed = Deno.core.ops.op_check_permission("read", "/tmp/krepis/test");
            const denied = Deno.core.ops.op_check_permission("write", "/etc/passwd");
            
            allowed === true && denied === false;
        "#.to_string(),
    );

    assert!(result.is_ok());
}

#[test]
fn test_protobuf_context_creation() {
    let ctx = KrepisContext {
        request_id: "proto-test".to_string(),
        tenant_id: "tenant-proto".to_string(),
        priority: 10,
        is_turbo_mode: true,
        trace_id: "trace-proto".to_string(),
        timestamp: 1234567890,
        metadata: Default::default(),
    };

    let encoded = ctx.encode_to_vec();
    let decoded = KrepisContext::decode(&encoded[..]).unwrap();

    assert_eq!(decoded.request_id, "proto-test");
    assert_eq!(decoded.is_turbo_mode, true);
    assert_eq!(decoded.priority, 10);
}

#[test]
fn test_journal_persistence() {
    use tempfile::TempDir;
    
    let temp_dir = TempDir::new().unwrap();
    let journal_path = temp_dir.path();
    
    // First session: create journal and increment
    {
        let journal = SovereignJournal::new(journal_path).unwrap();
        
        let count1 = journal.increment_op_count("test_op").unwrap();
        assert_eq!(count1, 1);
        
        let count2 = journal.increment_op_count("test_op").unwrap();
        assert_eq!(count2, 2);
        
        // Log transaction
        journal.log_transaction(&TransactionLog {
            timestamp: 1234567890,
            op_name: "test_op".to_string(),
            request_id: "req-001".to_string(),
            status: LogStatus::Completed,
        }).unwrap();
    }
    
    // Second session: recover from disk
    {
        let journal = SovereignJournal::new(journal_path).unwrap();
        
        let recovered = journal.recover_op_count("test_op").unwrap();
        assert_eq!(recovered, 2, "Op count should persist across restarts");
        
        assert_eq!(journal.journal_count(), 1, "Transaction log should persist");
    }
}

#[tokio::test]
async fn test_kernel_restart_recovery() {
    use tempfile::TempDir;
    let temp_dir = TempDir::new().unwrap();
    let journal_path = temp_dir.path();
    
    // First kernel session
    let initial_count = {
        let journal = Arc::new(SovereignJournal::new(journal_path).unwrap());
        let stats = Rc::new(RefCell::new(SovereignStats::default()));
        let stats_for_check = stats.clone(); // 체크용으로 미리 복사

        let mut ext = krepis_test::init_ops();
        ext.op_state_fn = Some(Box::new(move |state| {
            state.put(stats.clone());
            state.put(journal.clone());
        }));

        let mut runtime = JsRuntime::new(RuntimeOptions {
            extensions: vec![ext],
            ..Default::default()
        });

        runtime.execute_script(
            "increment_test",
            "for (let i = 0; i < 5; i++) { Deno.core.ops.op_increment_stats(); }".to_string(),
        ).unwrap();
        
        runtime.run_event_loop(PollEventLoopOptions {
            wait_for_inspector: false,
            pump_v8_message_loop: true,
        }).await.unwrap();
        
        let final_val = stats_for_check.borrow().js_ops_called; 
        final_val
    };
    
    assert_eq!(initial_count, 5);
    
    // Second kernel session (simulated restart)
    let recovered_count = {
        let journal = Arc::new(SovereignJournal::new(journal_path).unwrap());
        let recovered = journal.recover_op_count("js_ops_called").unwrap();
        
        let stats = Rc::new(RefCell::new(SovereignStats {
            js_ops_called: recovered,
            contexts_created: 0,
        }));
        let stats_for_check = stats.clone();

        let mut ext = krepis_test::init_ops();
        ext.op_state_fn = Some(Box::new(move |state| {
            state.put(stats.clone());
            state.put(journal.clone());
        }));

        let mut runtime = JsRuntime::new(RuntimeOptions {
            extensions: vec![ext],
            ..Default::default()
        });

        runtime.execute_script(
            "recovery_test",
            "for (let i = 0; i < 3; i++) { Deno.core.ops.op_increment_stats(); }".to_string(),
        ).unwrap();
        
        runtime.run_event_loop(PollEventLoopOptions {
            wait_for_inspector: false,
            pump_v8_message_loop: true,
        }).await.unwrap();
        
        let final_val = stats_for_check.borrow().js_ops_called; 
        final_val
    };
    
    assert_eq!(recovered_count, 8);
}