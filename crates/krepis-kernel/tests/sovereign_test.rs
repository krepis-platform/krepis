use deno_core::{JsRuntime, RuntimeOptions, PollEventLoopOptions};
use std::rc::Rc;
use std::cell::RefCell;
use std::sync::Arc;
use prost::Message;

// Trinity 계층에서 필요한 요소들
use krepis_kernel::proto::KrepisContext;
use krepis_kernel::domain::journal::{TransactionLog, LogStatus};
use krepis_kernel::adapters::storage::SovereignJournal;
use krepis_kernel::runtime_ops::{self, SovereignStats};

deno_core::extension!(
    krepis_test,
    ops = [
        runtime_ops::bridge::op_get_context,
        runtime_ops::bridge::op_check_permission,
        runtime_ops::bridge::op_increment_stats,
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
    use krepis_kernel::domain::tenant::{TenantMetadata, TenantTier};
    use tempfile::TempDir;
    
    let ctx_buffer: Rc<Vec<u8>> = Rc::new(vec![]);
    let temp_dir = TempDir::new().unwrap();
    let journal = Arc::new(SovereignJournal::new(temp_dir.path()).unwrap());
    let tenant_meta = TenantMetadata::new("test-tenant".to_string(), TenantTier::Standard);

    let mut ext = krepis_test::init_ops();
    ext.op_state_fn = Some(Box::new(move |state| {
        state.put(ctx_buffer.clone());
        state.put(journal.clone());
        state.put(tenant_meta.clone());
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

/// 💡 C-001 Fix: 테넌트 격리 저널 테스트
#[test]
fn test_journal_persistence_with_tenant_isolation() {
    use tempfile::TempDir;
    
    let temp_dir = TempDir::new().unwrap();
    let journal_path = temp_dir.path();
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // First session: 테넌트별 격리된 데이터 생성
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    {
        let journal = SovereignJournal::new(journal_path).unwrap();
        
        // 💡 C-001 Fix: tenant_id를 첫 번째 인자로 전달
        let count1 = journal.increment_op_count("tenant-alpha", "test_op").unwrap();
        assert_eq!(count1, 1);
        
        let count2 = journal.increment_op_count("tenant-alpha", "test_op").unwrap();
        assert_eq!(count2, 2);
        
        // 다른 테넌트도 동일한 op_name을 가질 수 있지만 격리됨
        let count_beta = journal.increment_op_count("tenant-beta", "test_op").unwrap();
        assert_eq!(count_beta, 1, "tenant-beta should have isolated counter");
        
        // 💡 C-001 Fix: tenant_id를 첫 번째 인자로 전달
        journal.log_transaction("tenant-alpha", &TransactionLog {
            timestamp: 1234567890,
            op_name: "test_op".to_string(),
            request_id: "req-001".to_string(),
            status: LogStatus::Completed,
        }).unwrap();
    }
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // Second session: 디스크에서 복구 및 격리 검증
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    {
        let journal = SovereignJournal::new(journal_path).unwrap();
        
        // 💡 테넌트별 격리 검증
        let recovered_alpha = journal.recover_op_count("tenant-alpha", "test_op").unwrap();
        assert_eq!(recovered_alpha, 2, "tenant-alpha op count should persist");
        
        let recovered_beta = journal.recover_op_count("tenant-beta", "test_op").unwrap();
        assert_eq!(recovered_beta, 1, "tenant-beta op count should be isolated");
        
        // 존재하지 않는 테넌트는 0
        let recovered_gamma = journal.recover_op_count("tenant-gamma", "test_op").unwrap();
        assert_eq!(recovered_gamma, 0, "non-existent tenant should return 0");
        
        // 💡 C-001 Fix: journal_count도 tenant_id 필요
        assert_eq!(journal.journal_count("tenant-alpha").unwrap(), 1, "Transaction log should persist");
        assert_eq!(journal.journal_count("tenant-beta").unwrap(), 0, "tenant-beta has no logs");
    }
}

/// 💡 C-001 Fix: 크로스-테넌트 격리 검증 테스트
#[test]
fn test_cross_tenant_isolation() {
    use tempfile::TempDir;
    
    let temp_dir = TempDir::new().unwrap();
    let journal = SovereignJournal::new(temp_dir.path()).unwrap();
    
    // Tenant A: 민감한 데이터 저장
    journal.log_transaction("tenant-a", &TransactionLog {
        timestamp: 1000,
        op_name: "sensitive_operation".to_string(),
        request_id: "secret-req-123".to_string(),
        status: LogStatus::Completed,
    }).unwrap();
    
    // Tenant B: 자신의 데이터만 접근 가능
    let logs_b = journal.get_recent_logs("tenant-b", 100).unwrap();
    assert_eq!(logs_b.len(), 0, "Tenant B should not see Tenant A's logs");
    
    // Tenant A: 자신의 데이터 접근 가능
    let logs_a = journal.get_recent_logs("tenant-a", 100).unwrap();
    assert_eq!(logs_a.len(), 1, "Tenant A should see own logs");
    assert_eq!(logs_a[0].request_id, "secret-req-123");
}

#[tokio::test]
async fn test_kernel_restart_recovery_with_tenant_isolation() {
    use tempfile::TempDir;
    use krepis_kernel::domain::tenant::{TenantMetadata, TenantTier};
    
    let temp_dir = TempDir::new().unwrap();
    let journal_path = temp_dir.path();
    const TEST_TENANT: &str = "recovery-test-tenant";
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // First kernel session
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let initial_count = {
        let journal = Arc::new(SovereignJournal::new(journal_path).unwrap());
        let stats = Rc::new(RefCell::new(SovereignStats::default()));
        let stats_for_check = stats.clone();
        let tenant_meta = TenantMetadata::new(TEST_TENANT.to_string(), TenantTier::Standard);

        let mut ext = krepis_test::init_ops();
        ext.op_state_fn = Some(Box::new(move |state| {
            state.put(stats.clone());
            state.put(journal.clone());
            state.put(tenant_meta.clone());
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
        
        let count = stats_for_check.borrow().js_ops_called;
        count
    };
    
    assert_eq!(initial_count, 5);
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // Second kernel session (simulated restart)
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let recovered_count = {
        let journal = Arc::new(SovereignJournal::new(journal_path).unwrap());
        
        // 💡 C-001 Fix: tenant_id 전달하여 격리된 데이터 복구
        let recovered = journal.recover_op_count(TEST_TENANT, "js_ops_called").unwrap();
        
        let stats = Rc::new(RefCell::new(SovereignStats {
            js_ops_called: recovered,
            contexts_created: 0,
        }));
        let stats_for_check = stats.clone();
        let tenant_meta = TenantMetadata::new(TEST_TENANT.to_string(), TenantTier::Standard);

        let mut ext = krepis_test::init_ops();
        ext.op_state_fn = Some(Box::new(move |state| {
            state.put(stats.clone());
            state.put(journal.clone());
            state.put(tenant_meta.clone());
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
        
        let count = stats_for_check.borrow().js_ops_called;
        count
    };
    
    // 5 (recovered) + 3 (new) = 8
    assert_eq!(recovered_count, 8);
}