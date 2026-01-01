use anyhow::{Result};
use deno_core::{JsRuntime, RuntimeOptions};
use lru::LruCache;
use parking_lot::Mutex;
use std::num::NonZeroUsize;
use std::rc::Rc;
use std::cell::RefCell;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tracing::{info};

use crate::adapters::storage::SovereignJournal;
use crate::domain::tenant::{TenantMetadata, TenantTier};
use crate::domain::now_ms;
// Domain 계층의 순수 정책을 가져옴
use crate::domain::pool::PoolPolicy;
use crate::ops::{self, SovereignStats};

/// [Hexagonal Adapter] Sovereign Pool
/// 외부 의존성(V8, Sled)을 실질적으로 제어하는 어댑터 레이어
pub struct SovereignPool {
    pool: Mutex<LruCache<String, PooledRuntime>>,
    tenant_cache: Mutex<LruCache<String, TenantMetadata>>,
    journal: Arc<SovereignJournal>,
    config: PoolConfig,
}

#[derive(Debug, Clone)]
pub struct PoolConfig {
    pub max_pool_size: usize,
    pub max_idle_time: Duration,
    pub default_tier: TenantTier,
}

impl Default for PoolConfig {
    fn default() -> Self {
        Self {
            max_pool_size: 100,
            max_idle_time: Duration::from_secs(300),
            default_tier: TenantTier::Free,
        }
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
    pub fn new(journal: Arc<SovereignJournal>, config: PoolConfig) -> Self {
        let pool_size = NonZeroUsize::new(config.max_pool_size).expect("Invalid pool size");
        let tenant_size = NonZeroUsize::new(1000).unwrap();
        
        info!("🏊 Sovereign Pool (Hexagonal Adapter) initialized");
        
        Self {
            pool: Mutex::new(LruCache::new(pool_size)),
            tenant_cache: Mutex::new(LruCache::new(tenant_size)),
            journal,
            config,
        }
    }

    /// [Command] Isolate 확보
    pub fn acquire(&self, tenant_id: &str) -> Result<RuntimeGuard<'_>> {
        let tenant = self.get_tenant_metadata(tenant_id)?;
        tenant.validate()?; // Domain 로직 호출
        
        let mut pool = self.pool.lock();
        
        let pooled = match pool.pop(tenant_id) {
            Some(mut cached) => {
                info!("♻️ Reusing warm isolate: {}", tenant_id);
                cached.touch();
                cached
            }
            None => {
                info!("🆕 Creating new isolate: {}", tenant_id);
                PooledRuntime::new(self.create_runtime(&tenant)?)
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
            // Domain의 ResourceConfig를 참고하여 우선순위 결정 가능
            priority: 1, 
            timestamp: now_ms(),
            ..Default::default()
        };
        
        let ctx_buffer = Rc::new(prost::Message::encode_to_vec(&ctx_data));
        let stats = Rc::new(RefCell::new(SovereignStats::default()));
        
        // 2. Extension 초기화 (v0.316 매크로 방식 준수)
        let mut ext = ops::krepis_sovereign::init_ops();
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

        // 1. 제거할 대상의 ID만 먼저 수집 (Immutable borrow)
        for (tid, pooled) in pool.iter() {
            if PoolPolicy::should_evict(pooled.last_used, max_idle) {
                to_remove.push(tid.clone());
            }
        }

        // 2. 수집된 ID들을 제거 (Mutable borrow)
        for tid in to_remove {
            pool.pop(&tid);
            info!("🗑️  Evicted: {}", tid);
        }
    }

    pub fn release(&self, tenant_id: String, pooled: PooledRuntime) {
        if tenant_id.is_empty() { return; }
        
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

    fn get_tenant_metadata(&self, tenant_id: &str) -> Result<TenantMetadata> {
        let mut cache = self.tenant_cache.lock();
        if let Some(meta) = cache.get(tenant_id) {
            return Ok(meta.clone());
        }
        let meta = TenantMetadata::new(tenant_id.to_string(), self.config.default_tier);
        cache.put(tenant_id.to_string(), meta.clone());
        Ok(meta)
    }

    /// [Helper] 특정 테넌트의 런타임을 획득하여 클로저를 실행하고 자동 반환합니다.
    pub async fn execute_isolated<F, R>(&self, tenant_id: &str, f: F) -> Result<R>
    where
        F: FnOnce(&mut deno_core::JsRuntime) -> Result<R>,
    {
        let mut guard = self.acquire(tenant_id)?;
        let result = f(guard.runtime_mut());

        // 💡 추가: 결과가 에러일 경우 저널에 자동으로 기록
        if let Err(ref e) = result {
            let _ = self.journal.log_transaction(&crate::domain::journal::TransactionLog {
                timestamp: crate::domain::now_ms(),
                op_name: format!("{}:panic_caught", tenant_id),
                request_id: "internal-fault-handler".to_string(),
                status: crate::domain::journal::LogStatus::Failed,
            });
            tracing::error!("🛡️ Internal Fault Handled for {}: {}", tenant_id, e);
        }

        result
    }

    /// [System] 테스트 종료 시 V8 스택 순서(LIFO)를 지키며 자원을 해제하기 위한 메서드
    pub fn shutdown(&self) {
        let mut pool = self.pool.lock();
        let mut items = Vec::new();

        // 1. 캐시에 있는 모든 런타임을 꺼냅니다.
        // pop_lru()는 가장 오래된(Least Recently Used) 것부터 나옵니다.
        // 예: [A, B] 순서로 나옴
        while let Some((_id, runtime)) = pool.pop_lru() {
            items.push(runtime);
        }

        // 2. 현재 items는 [Oldest, ..., Newest] 순서입니다.
        // V8 스택은 Newest가 Top에 있으므로, Newest부터 드롭해야 합니다.
        // 배열을 뒤집습니다. -> [Newest, ..., Oldest]
        items.reverse();

        // 3. items 벡터가 스코프를 벗어나면서 0번 인덱스(Newest)부터 차례로 드롭됩니다.
        // V8: "편-안"
        info!("🛑 Sovereign Pool shutdown: {} isolates dropped safely.", items.len());
    }
}

/// [RAII Guard] 런타임 수명 관리
pub struct RuntimeGuard<'a> {
    runtime: Option<PooledRuntime>,
    tenant_id: String,
    pool_ref: &'a SovereignPool,
}

impl<'a> RuntimeGuard<'a> {
    pub fn runtime_mut(&mut self) -> &mut JsRuntime {
        &mut self.runtime.as_mut().unwrap().runtime
    }
    pub fn leak(&mut self) { self.runtime.take(); }
}

impl<'a> Drop for RuntimeGuard<'a> {
    fn drop(&mut self) {
        if let Some(mut pooled) = self.runtime.take() {
            // 💡 현재 시점의 시간을 업데이트하여 반환
            pooled.last_used = std::time::Instant::now();
            
            // tenant_id 소유권을 완전히 이전하며 release 호출
            let tid = std::mem::take(&mut self.tenant_id);
            self.pool_ref.release(tid, pooled);
        }
    }
}