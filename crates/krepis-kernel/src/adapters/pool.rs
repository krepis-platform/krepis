use anyhow::Result;
use dashmap::DashMap;
use deno_core::{JsRuntime, RuntimeOptions};
use lru::LruCache;
use parking_lot::Mutex;
use std::cell::RefCell;
use std::num::NonZeroUsize;
use std::rc::Rc;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Duration, Instant};
use tokio::sync::{OwnedSemaphorePermit, Semaphore};
use tracing::{info, warn, error};
use deno_core::v8;

use crate::adapters::storage::SovereignJournal;
use crate::domain::{LogStatus, TransactionLog, now_ms};
use crate::domain::pool::PoolPolicy;
use crate::domain::tenant::{TenantError, TenantMetadata, TenantTier};
use crate::runtime_ops::{self, SovereignStats};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [Hexagonal Adapter] Sovereign Pool with C-002 Bulkhead Pattern
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/// [Hexagonal Adapter] Sovereign Pool
/// 
/// V8 Isolate 풀링과 테넌트별 동시성 제어(Bulkhead)를 담당하는 어댑터 레이어입니다.
/// 
/// # C-002 Compliance: Bulkhead Pattern
/// 
/// 각 테넌트는 자신의 등급(`TenantTier`)에 따라 할당된 동시 실행 슬롯을 가지며,
/// `tokio::sync::Semaphore`를 통해 RAII 방식으로 관리됩니다.
/// 
/// - Free: 5 concurrent requests
/// - Standard: 20 concurrent requests  
/// - Enterprise: 100 concurrent requests
/// 
/// # Spec-003 Compliance: Concurrency & Throttling
/// 
/// 동시 실행 한도 초과 시 즉시 `TenantError::QuotaExceeded`를 반환하거나,
/// `acquire_timeout` 동안 대기 후 `TenantError::AcquireTimeout`을 반환합니다.
pub struct SovereignPool {
    /// LRU 캐시 기반 V8 Isolate 풀
    pool: Mutex<LruCache<String, PooledRuntime>>,
    
    /// 테넌트 메타데이터 캐시
    tenant_cache: Mutex<LruCache<String, TenantMetadata>>,
    
    /// 트랜잭션 저널 (테넌트 격리)
    journal: Arc<SovereignJournal>,
    
    /// 풀 설정
    config: PoolConfig,
    
    /// C-002: 테넌트별 동시성 제어 세마포어
    /// 
    /// Key: tenant_id
    /// Value: Arc<Semaphore> (permits = max_concurrent_requests)
    /// 
    /// DashMap을 사용하여 락 없이 동시 접근 가능
    semaphores: DashMap<String, Arc<Semaphore>>,
}

/// Pool 설정
/// 
/// # C-002 Enhancement
/// `acquire_timeout` 필드 추가 - 세마포어 획득 대기 시간
#[derive(Debug, Clone)]
pub struct PoolConfig {
    /// 최대 풀 크기 (캐시된 Isolate 수)
    pub max_pool_size: usize,
    
    /// 유휴 Isolate 최대 유지 시간
    pub max_idle_time: Duration,
    
    /// 신규 테넌트 기본 등급
    pub default_tier: TenantTier,
    
    /// C-002: 세마포어 획득 타임아웃
    /// 
    /// 즉시 획득 실패 시, 이 시간만큼 대기 후 타임아웃 에러 반환
    pub acquire_timeout: Duration,
}

impl Default for PoolConfig {
    fn default() -> Self {
        Self {
            max_pool_size: 100,
            max_idle_time: Duration::from_secs(300),
            default_tier: TenantTier::Free,
            acquire_timeout: Duration::from_secs(5),
        }
    }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// C-003: V8 Termination Handle (Watchdog 지원)
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/// V8 Isolate 강제 종료 핸들
/// 
/// # Safety
/// V8의 `terminate_execution()`은 다른 스레드에서 호출해도 안전합니다.
/// 이 핸들은 Watchdog 타이머가 실행 시간 초과 시 Isolate를 중단하는 데 사용됩니다.
#[derive(Clone)]
pub struct V8TerminationHandle {
    isolate_ptr: *mut v8::Isolate,
    terminated: Arc<AtomicBool>,
}

// V8 Isolate 포인터는 terminate_execution 호출에 한해 스레드 안전함
unsafe impl Send for V8TerminationHandle {}
unsafe impl Sync for V8TerminationHandle {}

impl V8TerminationHandle {
    /// 새로운 Termination Handle 생성
    ///
    /// # Safety
    /// 'runtime'은 이 핸들의 수명 동안 유효해야 합니다.
    fn new(runtime: &mut JsRuntime) -> Self {
        Self {
            isolate_ptr: runtime.v8_isolate().as_mut() as *mut v8::Isolate,
            terminated: Arc::new(AtomicBool::new(false)),
        }
    }

    /// V8 Isolate 실행 강제 중단
    /// 
    /// # Spec-003 Compliance: Execution Guard (Watchdog)
    /// 이 메서드는 Watchdog 타이머에서 호출되어 무한 루프를 방지합니다.
    pub fn terminate(&self) {
        if !self.terminated.swap(true, Ordering::SeqCst) {
            // Safety: V8의 terminate_execution은 스레드 안전함
            unsafe {
                (*self.isolate_ptr).terminate_execution();
            }
            warn!("⚡ V8 Isolate terminated by Watchdog");
        }
    }
    
    /// 이 Isolate가 종료되었는지 확인
    pub fn is_terminated(&self) -> bool {
        self.terminated.load(Ordering::SeqCst)
    }
}

/// V8 Isolate를 포함하는 물리적 엔티티
pub struct PooledRuntime {
    runtime: JsRuntime,
    last_used: Instant,
    request_count: u64,
}

impl PooledRuntime {
    fn new(runtime: JsRuntime) -> Self {
        Self {
            runtime,
            last_used: Instant::now(),
            request_count: 0,
        }
    }

    fn touch(&mut self) {
        self.last_used = Instant::now();
        self.request_count += 1;
    }
}

impl SovereignPool {
    /// 새로운 SovereignPool 인스턴스 생성
    pub fn new(journal: Arc<SovereignJournal>, config: PoolConfig) -> Self {
        let pool_size = NonZeroUsize::new(config.max_pool_size).expect("Invalid pool size");
        let tenant_size = NonZeroUsize::new(1000).unwrap();

        info!("🏊 Sovereign Pool initialized with Bulkhead pattern (C-002)");
        info!("   └─ Acquire timeout: {:?}", config.acquire_timeout);

        Self {
            pool: Mutex::new(LruCache::new(pool_size)),
            tenant_cache: Mutex::new(LruCache::new(tenant_size)),
            journal,
            config,
            semaphores: DashMap::new(),
        }
    }

    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // C-002: Bulkhead Pattern - Semaphore Management
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    /// [C-002] 테넌트별 세마포어 획득 또는 생성
    /// 
    /// DashMap의 entry API를 사용하여 원자적으로 세마포어를 생성하거나 기존 것을 반환합니다.
    /// 
    /// # Arguments
    /// * `tenant_id` - 테넌트 식별자
    /// * `max_permits` - 최대 동시 실행 수 (Tier에서 결정)
    fn get_or_create_semaphore(&self, tenant_id: &str, max_permits: usize) -> Arc<Semaphore> {
        self.semaphores
            .entry(tenant_id.to_string())
            .or_insert_with(|| {
                info!("🚦 Creating semaphore for tenant {} (permits: {})", tenant_id, max_permits);
                Arc::new(Semaphore::new(max_permits))
            })
            .value()
            .clone()
    }

    /// [C-002] 세마포어 permit 획득 (RAII)
    /// 
    /// 즉시 획득을 시도하고, 실패 시 타임아웃까지 대기합니다.
    /// 
    /// # Returns
    /// * `Ok(OwnedSemaphorePermit)` - Drop 시 자동으로 permit 반환
    /// * `Err(TenantError::QuotaExceeded)` - 즉시 획득 실패 시 (정보 제공용)
    /// * `Err(TenantError::AcquireTimeout)` - 타임아웃 초과 시
    /// 
    /// # RAII Safety
    /// `OwnedSemaphorePermit`은 Drop trait을 구현하여 스코프를 벗어나면
    /// 자동으로 permit이 반환됩니다. 패닉이 발생해도 안전합니다.
    async fn acquire_permit(
        &self,
        tenant_id: &str,
        semaphore: Arc<Semaphore>,
        max_permits: usize,
    ) -> Result<OwnedSemaphorePermit, TenantError> {
        // 1. 즉시 획득 시도 (Non-blocking)
        match Arc::clone(&semaphore).try_acquire_owned() {
            Ok(permit) => {
                info!("✅ Permit acquired immediately for {}", tenant_id);
                return Ok(permit);
            }
            Err(_) => {
                // 현재 사용 중인 슬롯 수 계산
                let current = max_permits - semaphore.available_permits();
                warn!(
                    "⏳ Tenant {} at capacity ({}/{}), waiting...",
                    tenant_id, current, max_permits
                );
            }
        }

        // 2. 타임아웃 대기 (Blocking with timeout)
        match tokio::time::timeout(self.config.acquire_timeout, semaphore.acquire_owned()).await {
            Ok(Ok(permit)) => {
                info!("✅ Permit acquired after wait for {}", tenant_id);
                Ok(permit)
            }
            Ok(Err(_)) => {
                // 세마포어가 닫힌 경우 (정상적으로는 발생하지 않음)
                Err(TenantError::AcquireTimeout(tenant_id.to_string()))
            }
            Err(_) => {
                // 주의: 여기서 semaphore를 다시 쓰려면 위 timeout 호출 시에도 clone을 했어야 합니다.
                // 하지만 사용량이 max_permits와 같다고 간주할 수 있으므로 숫자로 처리합니다.
                warn!(
                    "⏰ Permit acquisition timed out for {} ({}/{})",
                    tenant_id, max_permits, max_permits
                );
                Err(TenantError::AcquireTimeout(tenant_id.to_string()))
            }
        }
    }

    /// [C-002 Query] 특정 테넌트의 현재 활성 요청 수 조회
    /// 
    /// 모니터링 및 디버깅 용도로 사용됩니다.
    pub fn active_requests(&self, tenant_id: &str) -> Option<usize> {
        self.semaphores.get(tenant_id).map(|entry| {
            let semaphore = entry.value();
            let tenant = self.get_tenant_metadata(tenant_id).ok()?;
            let max = tenant.resource_config().max_concurrent_requests;
            Some(max - semaphore.available_permits())
        })?
    }

    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // Core Pool Operations
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    /// [Command] Isolate 확보 (동기)
    /// 
    /// 주의: 이 메서드는 Bulkhead 제어를 거치지 않습니다.
    /// 동시성 제어가 필요한 경우 `execute_isolated()`를 사용하세요.
    pub fn acquire(&self, tenant_id: &str) -> Result<RuntimeGuard<'_>, TenantError> {
        let tenant = self.get_tenant_metadata(tenant_id)
            .map_err(|e| TenantError::Internal(format!("Metadata cache error: {}", e)))?;
        tenant.validate()?;

        let mut pool = self.pool.lock();

        let pooled = match pool.pop(tenant_id) {
            Some(mut cached) => {
                info!("♻️ Reusing warm isolate: {}", tenant_id);
                cached.touch();
                cached
            }
            None => {
                info!("🆕 Creating new isolate: {}", tenant_id);
                let runtime = self.create_runtime(&tenant)
                    .map_err(|e| TenantError::Internal(format!("V8 Isolate creation failed: {}", e)))?;
                PooledRuntime::new(runtime)
            }
        };

        Ok(RuntimeGuard {
            runtime: Some(pooled),
            tenant_id: tenant_id.to_string(),
            pool_ref: self,
        })
    }

    /// [Internal] V8 Runtime 물리적 생성
    fn create_runtime(&self, tenant: &TenantMetadata) -> Result<JsRuntime> {
        // 1. Context 준비 (Spec-002)
        let ctx_data = crate::proto::KrepisContext {
            request_id: uuid::Uuid::new_v4().to_string(),
            tenant_id: tenant.tenant_id.clone(),
            priority: 1,
            timestamp: now_ms(),
            ..Default::default()
        };

        let ctx_buffer = Rc::new(prost::Message::encode_to_vec(&ctx_data));
        let stats = Rc::new(RefCell::new(SovereignStats::default()));

        // 2. Extension 초기화 (v0.316 매크로 방식 준수)
        let mut ext = runtime_ops::krepis_sovereign::init_ops();
        let journal = self.journal.clone();
        let tenant_meta = tenant.clone();

        ext.op_state_fn = Some(Box::new(move |state| {
            state.put(ctx_buffer.clone());
            state.put(stats.clone());
            state.put(journal.clone());
            state.put(tenant_meta.clone());
        }));

        // 3. Runtime 생성
        let runtime = JsRuntime::new(RuntimeOptions {
            extensions: vec![ext],
            ..Default::default()
        });

        Ok(runtime)
    }

    /// [Command] 유휴 자원 정리 - Domain Policy에 의존
    pub fn cleanup_idle(&self) {
        let mut pool = self.pool.lock();
        let max_idle = self.config.max_idle_time;
        let mut to_remove = Vec::new();

        for (tid, pooled) in pool.iter() {
            if PoolPolicy::should_evict(pooled.last_used, max_idle) {
                to_remove.push(tid.clone());
            }
        }

        for tid in to_remove {
            pool.pop(&tid);
            info!("🗑️  Evicted: {}", tid);
        }
    }

    /// [Internal] Isolate 반환
    pub fn release(&self, tenant_id: String, pooled: PooledRuntime) {
        if tenant_id.is_empty() {
            return;
        }

        let mut pool = self.pool.lock();
        pool.put(tenant_id, pooled);
    }

    /// [Query] 현재 풀 상태 스냅샷
    pub fn stats(&self) -> crate::domain::pool::PoolSnapshot {
        let pool = self.pool.lock();
        crate::domain::pool::PoolSnapshot {
            cached_isolates: pool.len(),
            max_capacity: self.config.max_pool_size,
            healthy: true,
        }
    }

    /// [Internal] 테넌트 메타데이터 조회 (캐시)
    fn get_tenant_metadata(&self, tenant_id: &str) -> anyhow::Result<TenantMetadata> {
        let mut cache = self.tenant_cache.lock();
        if let Some(meta) = cache.get(tenant_id) {
            return Ok(meta.clone());
        }
        let meta = TenantMetadata::new(tenant_id.to_string(), self.config.default_tier);
        cache.put(tenant_id.to_string(), meta.clone());
        Ok(meta)
    }

    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // C-002: Primary Execution API with Bulkhead
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    /// [C-002 Primary] 테넌트 격리 실행 with Bulkhead
    /// 
    /// 테넌트별 동시성 제한(Bulkhead)을 적용하여 스크립트를 실행합니다.
    /// 
    /// # Spec-003 Compliance: Concurrency & Throttling
    /// 
    /// 1. 테넌트의 `max_concurrent_requests` 조회
    /// 2. 세마포어에서 permit 획득 (RAII)
    /// 3. Isolate에서 클로저 실행
    /// 4. 결과와 무관하게 permit 자동 반환 (Drop)
    /// 
    /// # Spec-003 Compliance: Execution Guard (Watchdog)
    /// 테넌트 티어별 `max_execution_time`을 초과하면 V8 Isolate가 강제 중단됩니다.
    /// 중단된 Isolate는 상태가 불안정하므로 풀에 반환하지 않고 폐기합니다.
    /// 
    /// # Error Handling
    /// 
    /// - `TenantError::QuotaExceeded`: 정보 제공용 (즉시 실패 시)
    /// - `TenantError::AcquireTimeout`: 타임아웃 초과
    /// - 실행 에러: 저널에 기록 후 전파
    /// 
    /// # Example
    /// 
    /// ```ignore
    /// let result = pool.execute_isolated("tenant-123", |runtime| {
    ///     runtime.execute_script("test", "1 + 1".to_string())?;
    ///     Ok(())
    /// }).await;
    /// ```
    pub async fn execute_isolated<F, R>(&self, tenant_id: &str, f: F) -> Result<R, TenantError>
    where
        F: FnOnce(&mut deno_core::JsRuntime) -> anyhow::Result<R>,
    {
        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        // 1. [C-002] 리소스 정책 조회
        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        let tenant = self.get_tenant_metadata(tenant_id)
            .map_err(|e| TenantError::Inactive(format!("Metadata error: {}", e)))?;
        let config = tenant.resource_config();

        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        // 2. [C-002] Bulkhead: Permit 획득 (RAII)
        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        let semaphore = self.get_or_create_semaphore(tenant_id, config.max_concurrent_requests);
        let _permit = self.acquire_permit(tenant_id, semaphore, config.max_concurrent_requests).await?;
        
        // 💡 RAII Safety: `_permit`이 스코프를 벗어나면 자동으로 반환됩니다.
        //    패닉이 발생해도 Drop이 호출되어 permit이 반환됩니다.

        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        // 3. Isolate 확보 및 실행
        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        let mut guard = self.acquire(tenant_id)?;
        let term_handle = V8TerminationHandle::new(guard.runtime_mut());
        let term_handle_clone = term_handle.clone();

        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        // 4. [C-003] Watchdog 타이머 생성
        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        let watchdog_tenant_id = tenant_id.to_string();
        let max_exec_time = config.max_execution_time;

        // OS 스레드를 직접 생성하여 V8 루프와 무관하게 동작하게 함
        std::thread::spawn(move || {
            std::thread::sleep(max_exec_time);
            // V8이 루프를 돌고 있어도 OS 스레드이므로 지정된 시간에 반드시 깨어납니다.
            if !term_handle_clone.is_terminated() {
                warn!("⏰ Physical Watchdog triggered for tenant: {} (limit: {:?})", 
                    watchdog_tenant_id, max_exec_time);
                term_handle_clone.terminate();
            }
        });

        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        // 5. 실행
        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        let start_time = Instant::now();
        let result = f(guard.runtime_mut())
            .map_err(|e| {
                TenantError::RuntimeError(format!("V8 Execution Error: {}", e))
            });
        let elapsed = start_time.elapsed();

        if result.is_ok() && !term_handle.is_terminated() {
            return result;
        }

        // 7. [C-003 결과 처리] 타임아웃 발생 시 Isolation 폐기
        if term_handle.is_terminated() {
            // 중단된 Isolate는 불안정 상태이므로 풀에 반환하지 않음
            guard.leak();

            // 저널에 타임아웃 기록
            let _ = self.journal.log_transaction(
                tenant_id,
                &TransactionLog {
                    timestamp: now_ms(),
                    op_name: format!("{}:execution_timeout", tenant_id),
                    request_id: format!("watchdog-{}", uuid::Uuid::new_v4()),
                    status: LogStatus::Failed,
                }
            );

            error!("💥 Tenant {} execution terminated after {:?} (limit: {:?})", 
                tenant_id, elapsed, config.max_execution_time);
            
            return Err(TenantError::ExecutionTimeout {
                tenant_id: tenant_id.to_string(),
                limit_ms: config.max_execution_time.as_millis() as u64,
                elapsed_ms: elapsed.as_millis() as u64,
            }.into());
        }

        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        // 7. 일반 에러 처리 (C-001 호환)
        // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
        if let Err(ref e) = result {
            let _ = self.journal.log_transaction(
                tenant_id,
                &TransactionLog {
                    timestamp: now_ms(),
                    op_name: format!("{}:execution_error", tenant_id),
                    request_id: "internal-fault-handler".to_string(),
                    status: LogStatus::Failed,
                }
            );
            error!("🛡️ Execution error for {}: {}", tenant_id, e);
        }

        result
    }

    /// [Internal] Bulkhead를 우회하는 실행 (테스트 전용)
    /// 
    /// 동시성 제한 없이 직접 실행합니다. 통합 테스트에서만 사용하세요.
    #[doc(hidden)]
    pub async fn execute_unguarded<F, R>(&self, tenant_id: &str, f: F) -> Result<R>
    where
        F: FnOnce(&mut deno_core::JsRuntime) -> Result<R>,
    {
        let mut guard = self.acquire(tenant_id)?;
        let result = f(guard.runtime_mut());

        if let Err(ref e) = result {
            let _ = self.journal.log_transaction(
                tenant_id,
                &crate::domain::journal::TransactionLog {
                    timestamp: crate::domain::now_ms(),
                    op_name: format!("{}:panic_caught", tenant_id),
                    request_id: "internal-fault-handler".to_string(),
                    status: crate::domain::journal::LogStatus::Failed,
                },
            );
            tracing::error!("🛡️ Internal Fault Handled for {}: {}", tenant_id, e);
        }

        result
    }

    /// [System] 풀 종료 및 자원 해제
    /// 
    /// V8 스택 순서(LIFO)를 지키며 Isolate를 해제하고,
    /// 세마포어 맵을 정리합니다.
    pub fn shutdown(&self) {
        // 1. 세마포어 맵 정리
        self.semaphores.clear();
        info!("🚦 Semaphore map cleared");

        // 2. V8 Isolate 정리 (LIFO 순서)
        let mut pool = self.pool.lock();
        let mut items = Vec::new();

        while let Some((_id, runtime)) = pool.pop_lru() {
            items.push(runtime);
        }

        items.reverse();

        info!(
            "🛑 Sovereign Pool shutdown: {} isolates dropped safely.",
            items.len()
        );
    }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// [RAII Guard] 런타임 수명 관리
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

/// [RAII Guard] 런타임 수명 관리
/// 
/// Drop 시 자동으로 Isolate를 풀에 반환합니다.
pub struct RuntimeGuard<'a> {
    runtime: Option<PooledRuntime>,
    tenant_id: String,
    pool_ref: &'a SovereignPool,
}

impl<'a> RuntimeGuard<'a> {
    /// 런타임 가변 참조 획득
    pub fn runtime_mut(&mut self) -> &mut JsRuntime {
        &mut self.runtime.as_mut().unwrap().runtime
    }

    /// 런타임을 풀에 반환하지 않고 누수시킴 (비정상 종료 시)
    pub fn leak(&mut self) {
        self.runtime.take();
    }
}

impl<'a> Drop for RuntimeGuard<'a> {
    fn drop(&mut self) {
        if let Some(mut pooled) = self.runtime.take() {
            pooled.last_used = std::time::Instant::now();
            let tid = std::mem::take(&mut self.tenant_id);
            self.pool_ref.release(tid, pooled);
        }
    }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// C-002: Unit Tests
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_semaphore_creation() {
        let semaphores: DashMap<String, Arc<Semaphore>> = DashMap::new();

        // 첫 번째 접근: 새로 생성
        let sem1 = semaphores
            .entry("tenant-1".to_string())
            .or_insert_with(|| Arc::new(Semaphore::new(5)))
            .value()
            .clone();

        assert_eq!(sem1.available_permits(), 5);

        // 두 번째 접근: 기존 것 반환
        let sem2 = semaphores
            .entry("tenant-1".to_string())
            .or_insert_with(|| Arc::new(Semaphore::new(10))) // 이건 무시됨
            .value()
            .clone();

        // 같은 세마포어여야 함 (permits가 5로 유지)
        assert_eq!(sem2.available_permits(), 5);
    }

    #[tokio::test]
    async fn test_permit_acquisition() {
        let semaphore = Arc::new(Semaphore::new(2));

        // 2개 획득 가능
        let _p1 = semaphore.clone().try_acquire_owned().unwrap();
        let _p2 = semaphore.clone().try_acquire_owned().unwrap();

        // 3번째는 실패
        assert!(semaphore.clone().try_acquire_owned().is_err());

        // p1 drop 후 다시 획득 가능
        drop(_p1);
        let _p3 = semaphore.clone().try_acquire_owned().unwrap();
        assert!(semaphore.clone().try_acquire_owned().is_err());
    }

    #[tokio::test]
    async fn test_quota_exceeded_timeout() {
        let semaphore = Arc::new(Semaphore::new(1));

        // 1개 획득
        let _p1 = semaphore.clone().try_acquire_owned().unwrap();

        // 타임아웃 테스트 (100ms)
        let start = Instant::now();
        let result =
            tokio::time::timeout(Duration::from_millis(100), semaphore.clone().acquire_owned())
                .await;

        assert!(result.is_err()); // 타임아웃
        assert!(start.elapsed() >= Duration::from_millis(100));
    }
}
