use anyhow::{Context, Result};
use sled::Db;
use std::path::Path;
use std::sync::Arc;
use tracing::info;
use crate::domain::journal::TransactionLog;

/// [Hexagonal Adapter] Sled-based Journal Storage with Tenant Isolation
/// 
/// # Spec-002 Compliance: Logical Partitioning
/// 
/// 각 테넌트는 자신만의 격리된 Sled Tree를 가집니다.
/// - Journal Tree: `tenant_{tenant_id}_journal`
/// - Stats Tree: `tenant_{tenant_id}_stats`
/// 
/// 이를 통해 테넌트 간 데이터 혼입(Cross-tenant contamination)을 물리적으로 차단합니다.
/// 
/// # Zero-Knowledge Storage
/// 
/// 테넌트 코드는 자신의 Tree 이름을 알 수 없으며,
/// 오직 `tenant_id`를 통해 추상화된 API로만 접근합니다.
pub struct SovereignJournal {
    db: Arc<Db>,
}

impl SovereignJournal {
    /// 새로운 SovereignJournal 인스턴스를 생성합니다.
    /// 
    /// # Arguments
    /// * `path` - Sled DB 저장 경로 (예: `./.krepis/storage`)
    pub fn new<P: AsRef<Path>>(path: P) -> Result<Self> {
        let db = sled::open(path.as_ref()).context("Failed to open Sled database")?;
        
        info!("📚 SovereignJournal initialized with tenant isolation");
        
        Ok(Self {
            db: Arc::new(db),
        })
    }

    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // Private: 테넌트별 Tree 획득 (Zero-Knowledge 보장)
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    /// [Private] 테넌트별 Journal Tree 획득
    /// 
    /// Tree 명명 규칙: `tenant_{tenant_id}_journal`
    fn get_journal_tree(&self, tenant_id: &str) -> Result<sled::Tree> {
        let tree_name = format!("tenant_{}_journal", tenant_id);
        self.db.open_tree(&tree_name)
            .context(format!("Failed to open journal tree for tenant: {}", tenant_id))
    }

    /// [Private] 테넌트별 Stats Tree 획득
    /// 
    /// Tree 명명 규칙: `tenant_{tenant_id}_stats`
    fn get_stats_tree(&self, tenant_id: &str) -> Result<sled::Tree> {
        let tree_name = format!("tenant_{}_stats", tenant_id);
        self.db.open_tree(&tree_name)
            .context(format!("Failed to open stats tree for tenant: {}", tenant_id))
    }

    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // Public API: Command Implementation (테넌트 격리)
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    /// [Command] 저널에 트랜잭션 로그를 기록합니다.
    /// 
    /// # Arguments
    /// * `tenant_id` - 테넌트 식별자 (격리 키)
    /// * `log` - 기록할 트랜잭션 로그
    /// 
    /// # Security
    /// 각 테넌트의 로그는 `tenant_{tenant_id}_journal` Tree에 격리 저장됩니다.
    pub fn log_transaction(&self, tenant_id: &str, log: &TransactionLog) -> Result<()> {
        let tree = self.get_journal_tree(tenant_id)?;
        let key = format!("{}:{}", log.timestamp, log.request_id);
        let value = serde_json::to_vec(log)?;
        tree.insert(key.as_bytes(), value)?;
        tree.flush()?;
        Ok(())
    }

    /// [Command] 특정 operation의 카운터를 원자적으로 증가시킵니다.
    /// 
    /// # Arguments
    /// * `tenant_id` - 테넌트 식별자 (격리 키)
    /// * `op_name` - 오퍼레이션 이름 (예: "js_ops_called")
    /// 
    /// # Returns
    /// 증가된 후의 카운터 값
    pub fn increment_op_count(&self, tenant_id: &str, op_name: &str) -> Result<u64> {
        let tree = self.get_stats_tree(tenant_id)?;
        let key = format!("op_count:{}", op_name);
        
        let new_count = tree.update_and_fetch(key.as_bytes(), |old| {
            let current = old
                .and_then(|b| b.try_into().ok().map(u64::from_le_bytes))
                .unwrap_or(0);
            Some((current + 1).to_le_bytes().to_vec())
        })?
        .map(|b| u64::from_le_bytes(b.as_ref().try_into().unwrap()))
        .unwrap_or(1);
        
        tree.flush()?;
        Ok(new_count)
    }

    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // Public API: Query Implementation (테넌트 격리)
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    /// [Query] 특정 operation의 카운터 값을 복구/조회합니다.
    /// 
    /// # Arguments
    /// * `tenant_id` - 테넌트 식별자 (격리 키)
    /// * `op_name` - 오퍼레이션 이름
    /// 
    /// # Returns
    /// 현재 카운터 값 (없으면 0)
    pub fn recover_op_count(&self, tenant_id: &str, op_name: &str) -> Result<u64> {
        let tree = self.get_stats_tree(tenant_id)?;
        let key = format!("op_count:{}", op_name);
        
        Ok(tree.get(key.as_bytes())?
            .and_then(|b| b.as_ref().try_into().ok().map(u64::from_le_bytes))
            .unwrap_or(0))
    }

    /// [Query] 특정 테넌트의 저널 엔트리 개수를 반환합니다.
    /// 
    /// # Arguments
    /// * `tenant_id` - 테넌트 식별자
    pub fn journal_count(&self, tenant_id: &str) -> Result<usize> {
        let tree = self.get_journal_tree(tenant_id)?;
        Ok(tree.len())
    }

    /// [Query] 특정 테넌트의 최근 로그를 조회합니다.
    /// 
    /// # Arguments
    /// * `tenant_id` - 테넌트 식별자
    /// * `limit` - 최대 조회 개수
    pub fn get_recent_logs(&self, tenant_id: &str, limit: usize) -> Result<Vec<TransactionLog>> {
        let tree = self.get_journal_tree(tenant_id)?;
        let mut logs = Vec::new();
        
        // 역순 순회 (최신 로그 먼저)
        for item in tree.iter().rev().take(limit) {
            let (_, value) = item?;
            if let Ok(log) = serde_json::from_slice::<TransactionLog>(&value) {
                logs.push(log);
            }
        }
        
        Ok(logs)
    }

    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // Admin API: Enterprise 전용 (테넌트에게 노출 금지)
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    /// [Admin] 모든 테넌트의 Tree 목록 조회
    /// 
    /// # Security Warning
    /// 이 메서드는 Enterprise Admin API에서만 호출되어야 합니다.
    /// 일반 테넌트에게 노출되면 보안 위반입니다.
    pub fn list_tenant_trees(&self) -> Vec<String> {
        self.db.tree_names()
            .into_iter()
            .filter_map(|name| String::from_utf8(name.to_vec()).ok())
            .filter(|name| name.starts_with("tenant_"))
            .collect()
    }

    /// [Admin] 특정 테넌트의 모든 데이터 삭제
    /// 
    /// # Arguments
    /// * `tenant_id` - 삭제할 테넌트 식별자
    /// 
    /// # Security Warning
    /// 이 메서드는 테넌트 계정 삭제 시에만 호출되어야 합니다.
    pub fn delete_tenant_data(&self, tenant_id: &str) -> Result<()> {
        let journal_tree_name = format!("tenant_{}_journal", tenant_id);
        let stats_tree_name = format!("tenant_{}_stats", tenant_id);
        
        // Tree가 존재하면 삭제
        let _ = self.db.drop_tree(&journal_tree_name);
        let _ = self.db.drop_tree(&stats_tree_name);
        
        self.db.flush()?;
        
        info!("🗑️ Deleted all data for tenant: {}", tenant_id);
        Ok(())
    }

    /// [Admin] 전체 저널 항목 수 (모든 테넌트 합산)
    /// 
    /// # Security Warning
    /// 이 정보는 시스템 모니터링 목적으로만 사용되어야 합니다.
    pub fn total_journal_count(&self) -> usize {
        self.list_tenant_trees()
            .iter()
            .filter(|name| name.ends_with("_journal"))
            .filter_map(|name| self.db.open_tree(name).ok())
            .map(|tree| tree.len())
            .sum()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;
    use crate::domain::journal::LogStatus;

    #[test]
    fn test_tenant_isolation() {
        let temp_dir = TempDir::new().unwrap();
        let journal = SovereignJournal::new(temp_dir.path()).unwrap();
        
        // Tenant A: 카운터 증가
        journal.increment_op_count("tenant-a", "ops").unwrap();
        journal.increment_op_count("tenant-a", "ops").unwrap();
        
        // Tenant B: 카운터 증가
        journal.increment_op_count("tenant-b", "ops").unwrap();
        
        // 격리 검증: 각 테넌트는 자신만의 카운터를 가짐
        assert_eq!(journal.recover_op_count("tenant-a", "ops").unwrap(), 2);
        assert_eq!(journal.recover_op_count("tenant-b", "ops").unwrap(), 1);
        
        // 존재하지 않는 테넌트는 0 반환
        assert_eq!(journal.recover_op_count("tenant-c", "ops").unwrap(), 0);
    }

    #[test]
    fn test_journal_isolation() {
        let temp_dir = TempDir::new().unwrap();
        let journal = SovereignJournal::new(temp_dir.path()).unwrap();
        
        // Tenant A: 로그 기록
        journal.log_transaction("tenant-a", &TransactionLog {
            timestamp: 1000,
            op_name: "test".to_string(),
            request_id: "req-a".to_string(),
            status: LogStatus::Completed,
        }).unwrap();
        
        // Tenant B: 로그 기록
        journal.log_transaction("tenant-b", &TransactionLog {
            timestamp: 2000,
            op_name: "test".to_string(),
            request_id: "req-b".to_string(),
            status: LogStatus::Completed,
        }).unwrap();
        
        // 격리 검증
        assert_eq!(journal.journal_count("tenant-a").unwrap(), 1);
        assert_eq!(journal.journal_count("tenant-b").unwrap(), 1);
    }

    #[test]
    fn test_tree_naming_convention() {
        let temp_dir = TempDir::new().unwrap();
        let journal = SovereignJournal::new(temp_dir.path()).unwrap();
        
        // 데이터 생성
        journal.increment_op_count("prod-123", "test").unwrap();
        
        // Tree 이름 확인
        let trees = journal.list_tenant_trees();
        assert!(trees.contains(&"tenant_prod-123_stats".to_string()));
    }

    #[test]
    fn test_delete_tenant_data() {
        let temp_dir = TempDir::new().unwrap();
        let journal = SovereignJournal::new(temp_dir.path()).unwrap();
        
        // 테넌트 데이터 생성
        journal.increment_op_count("to-delete", "ops").unwrap();
        journal.log_transaction("to-delete", &TransactionLog {
            timestamp: 1000,
            op_name: "test".to_string(),
            request_id: "req".to_string(),
            status: LogStatus::Completed,
        }).unwrap();
        
        // 삭제 전 확인
        assert_eq!(journal.recover_op_count("to-delete", "ops").unwrap(), 1);
        
        // 테넌트 데이터 삭제
        journal.delete_tenant_data("to-delete").unwrap();
        
        // 삭제 후 확인 (새 Tree 생성되므로 0)
        assert_eq!(journal.recover_op_count("to-delete", "ops").unwrap(), 0);
    }
}