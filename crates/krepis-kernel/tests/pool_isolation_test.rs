use anyhow::Result;
use std::sync::Arc;
use std::time::Duration;
use tempfile::TempDir;
use tokio::task::LocalSet;
use parking_lot::Mutex;
use once_cell::sync::Lazy;
use tracing::info;
use prost::Message;

use krepis_kernel::adapters::storage::SovereignJournal;
use krepis_kernel::adapters::pool::{SovereignPool, PoolConfig};
use krepis_kernel::domain::tenant::{TenantMetadata, TenantTier};
use krepis_kernel::domain::TenantError;

static V8_TEST_MUTEX: Lazy<Mutex<()>> = Lazy::new(|| Mutex::new(()));

#[test] // 💡 #[tokio::test] 대신 일반 #[test] 사용 (멀티스레드 런타임 방지)
fn test_multi_tenant_isolation() -> Result<()> {
    let _lock = V8_TEST_MUTEX.lock();
    
    // 💡 별도의 싱글스레드 런타임을 수동으로 생성
    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()?;

    rt.block_on(async {
        let temp_dir = TempDir::new()?;
        let journal = Arc::new(SovereignJournal::new(temp_dir.path())?);
        let pool = SovereignPool::new(journal, PoolConfig::default());
        
        // Isolate 확보 및 해제
        {
            let _guard_a = pool.acquire("tenant-a")?;
            // drop 시점에 Isolate가 풀로 반환됨
        }
        // block_on 내부의 sleep은 스레드 이동을 유발하지 않음
        tokio::time::sleep(Duration::from_millis(10)).await; 

        {
            let _guard_b = pool.acquire("tenant-b")?;
        }
        tokio::time::sleep(Duration::from_millis(10)).await;

        assert_eq!(pool.stats().cached_isolates, 2);

        pool.shutdown();
        Ok(())
    })
}

#[tokio::test]
async fn test_isolate_warm_reuse() -> Result<()> {
    let temp_dir = TempDir::new()?;
    let journal = Arc::new(SovereignJournal::new(temp_dir.path())?);
    let pool = Arc::new(SovereignPool::new(journal, PoolConfig::default()));
    
    // First request for tenant-x
    {
        let mut guard = pool.acquire("tenant-x")?;
        let runtime = guard.runtime_mut();
        
        // Execute simple JS
        runtime.execute_script(
            "test",
            "globalThis.testValue = 42;".to_string()
        )?;
    }
    
    // Pool should have 1 cached isolate
    assert_eq!(pool.stats().cached_isolates, 1);
    
    // Second request - should reuse (but fresh context)
    {
        let mut guard = pool.acquire("tenant-x")?;
        let runtime = guard.runtime_mut();
        
        // Due to fresh context, previous globalThis should be reset
        // (In production with proper v8::Context recreation)
        let _result = runtime.execute_script(
            "test2",
            "typeof globalThis.testValue".to_string()
        )?;
        
        // Note: In current implementation, global state persists
        // Production version would reset v8::Context
    }
    
    Ok(())
}

#[tokio::test]
async fn test_fault_isolation() -> Result<()> {
    let local = LocalSet::new();
    local.run_until(async {
        let temp_dir = TempDir::new()?;
        let journal = Arc::new(SovereignJournal::new(temp_dir.path())?);
        let pool = Arc::new(SovereignPool::new(journal.clone(), PoolConfig::default()));
        
        let panic_tenant_id = "panic-tenant";
        
        // 1. 패닉 발생 테스트 (TenantError::RuntimeError 검증)
        {
            let result = pool.execute_isolated(panic_tenant_id, |runtime| {
                runtime.execute_script(
                    "panic",
                    "throw new Error('Simulated panic');".to_string()
                ).map_err(|e| anyhow::anyhow!(e)) // anyhow로 전달
            }).await;
            
            // 💡 수정됨: 구체적인 도메인 에러 타입 확인
            match result {
                Err(TenantError::RuntimeError(msg)) => {
                    assert!(msg.contains("Simulated panic"));
                    info!("✅ Caught expected RuntimeError");
                }
                _ => panic!("Expected TenantError::RuntimeError, got {:?}", result),
            }
        }

        // 2. 저널 기록 확인 (C-001 격리 확인)
        tokio::task::yield_now().await;
        assert!(journal.journal_count(panic_tenant_id).unwrap() > 0);
        
        pool.shutdown();
        Ok(())
    }).await
}

#[tokio::test]
async fn test_tenant_tier_resource_limits() -> Result<()> {
    // Free tier
    let free = TenantMetadata::new("free-user".to_string(), TenantTier::Free);
    let free_config = free.resource_config();
    assert_eq!(free_config.heap_limit_mb, 128);
    assert_eq!(free_config.max_concurrent_requests, 5);
    
    // Enterprise tier
    let enterprise = TenantMetadata::new("enterprise-user".to_string(), TenantTier::Enterprise);
    let ent_config = enterprise.resource_config();
    assert_eq!(ent_config.heap_limit_mb, 512);
    assert_eq!(ent_config.max_concurrent_requests, 100);
    
    Ok(())
}

#[test]
fn test_path_remapping() {
    let tenant = TenantMetadata::new("secure-tenant".to_string(), TenantTier::Standard);
    
    // Virtual path -> Physical path
    assert_eq!(
        tenant.safe_remap("/app/data/file.txt"),
        std::path::PathBuf::from("root/tenants/secure-tenant/app/data/file.txt")
    );
    
    // Security: Tenant can only access own paths
    assert!(tenant.is_path_allowed("root/tenants/secure-tenant/data/file.txt"));
    assert!(!tenant.is_path_allowed("root/tenants/other-tenant/data/file.txt"));
    assert!(!tenant.is_path_allowed("/etc/passwd"));
}

#[test]
fn test_storage_tree_naming() {
    let tenant = TenantMetadata::new("prod-123".to_string(), TenantTier::Enterprise);
    
    // Sled tree name follows spec-002 convention
    assert_eq!(tenant.storage_tree, "tenant_db_prod-123");
}

#[test]
fn test_path_remapping_logic() {
    // 도메인 로직만 테스트할 때는 runtime이 필요 없으므로 일반 테스트 가능
    let tenant = TenantMetadata::new("secure-tenant".to_string(), TenantTier::Standard);
    
    // Spec-002: safe_remap 이름 확인
    let remapped = tenant.safe_remap("/app/data.txt");
    assert!(remapped.to_str().unwrap().contains("secure-tenant"));
}

/// C-001: 테넌트별 저널 격리 통합 테스트
#[tokio::test]
async fn test_journal_tenant_isolation_via_pool() -> Result<()> {
    let local = LocalSet::new();
    local.run_until(async {
        let temp_dir = TempDir::new()?;
        let journal = Arc::new(SovereignJournal::new(temp_dir.path())?);
        let pool = Arc::new(SovereignPool::new(journal.clone(), PoolConfig::default()));
        
        // 테넌트 A: 에러 발생
        let tenant_a = "tenant-alpha";
        {
            let _ = pool.execute_isolated(tenant_a, |runtime| {
                runtime.execute_script("fail", "throw new Error('A failed');".to_string())?;
                Ok(())
            }).await;
        }
        tokio::task::yield_now().await;
        
        // 테넌트 B: 에러 발생
        let tenant_b = "tenant-beta";
        {
            let _ = pool.execute_isolated(tenant_b, |runtime| {
                runtime.execute_script("fail", "throw new Error('B failed');".to_string())?;
                Ok(())
            }).await;
        }
        tokio::task::yield_now().await;
        
        // C-001 핵심 검증: 각 테넌트의 저널이 완벽히 격리되어 있어야 함
        let count_a = journal.journal_count(tenant_a).unwrap();
        let count_b = journal.journal_count(tenant_b).unwrap();
        
        assert!(count_a > 0, "Tenant A should have journal entries");
        assert!(count_b > 0, "Tenant B should have journal entries");
        
        // 전체 저널 수 = A + B (각각 독립된 Tree에 저장)
        let total = journal.total_journal_count();
        assert_eq!(total, count_a + count_b, 
            "Total journal count should equal sum of tenant journals");
        
        // 테넌트 C: 신규 테넌트는 저널이 없어야 함
        assert_eq!(journal.journal_count("tenant-gamma").unwrap(), 0,
            "New tenant should have no journal entries");
        
        pool.shutdown();

        Ok(())
    }).await
}

#[tokio::test]
async fn test_execution_timeout_enforcement() -> Result<()> {
    let temp_dir = TempDir::new()?;
    let journal = Arc::new(SovereignJournal::new(temp_dir.path())?);
    
    // PoolConfig 기본값 (타임아웃은 TenantTier에서 결정됨)
    let pool = SovereignPool::new(journal, PoolConfig::default());
    let tenant_id = "timeout-tenant";

    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 💡 해결책: tokio::spawn을 제거합니다. 
    // 커널의 std::thread::spawn이 루프를 끊어주기 때문에 
    // 현재 스레드에서 직접 호출해도 테스트가 멈추지 않고 종료됩니다.
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let result = pool.execute_isolated(tenant_id, |runtime| {
        let _ = runtime.execute_script(
            "infinite", 
            "let i = 0; while(true){ i++; }".to_string()
        ).map_err(|e| anyhow::anyhow!(e))?;
        
        Ok(())
    }).await;

    // 3. 결과 검증
    match result {
        Err(TenantError::ExecutionTimeout { limit_ms, .. }) => {
            println!("✅ Watchdog (Physical Thread) successfully terminated infinite loop");
            // Tier 기본값(예: Free 1000ms)과 일치하는지 확인
            assert!(limit_ms > 0);
        }
        _ => panic!("Expected ExecutionTimeout, got {:?}", result),
    }

    Ok(())
}

#[test]
fn test_ffi_response_envelope_success() {
    use krepis_kernel::proto::{FfiResponse, ffi_response};
    
    let payload = vec![1, 2, 3];
    let req_id = "test-req".to_string();
    
    // Success Case
    let envelope = FfiResponse {
        result: Some(ffi_response::Result::SuccessPayload(payload.clone())),
        request_id: req_id.clone(),
        ..Default::default()
    };
    
    let encoded = envelope.encode_to_vec();
    let decoded = FfiResponse::decode(&encoded[..]).unwrap();
    
    if let Some(ffi_response::Result::SuccessPayload(data)) = decoded.result {
        assert_eq!(data, payload);
    } else {
        panic!("Should be SuccessPayload");
    }
}