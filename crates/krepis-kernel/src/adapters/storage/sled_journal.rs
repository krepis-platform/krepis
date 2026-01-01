use anyhow::{Context, Result};
use sled::{Db, Tree};
use std::path::Path;
use std::sync::Arc;
use crate::domain::journal::{TransactionLog};

/// [Hexagonal Adapter] Sled-based Journal Storage
pub struct SovereignJournal {
    db: Arc<Db>,
    journal_tree: Tree,
    stats_tree: Tree,
}

impl SovereignJournal {
    pub fn new<P: AsRef<Path>>(path: P) -> Result<Self> {
        let db = sled::open(path.as_ref()).context("Failed to open Sled database")?;
        let journal_tree = db.open_tree("journal")?;
        let stats_tree = db.open_tree("stats")?;
        
        Ok(Self {
            db: Arc::new(db),
            journal_tree,
            stats_tree,
        })
    }

    /// [Command Implementation] 저널 기록
    pub fn log_transaction(&self, log: &TransactionLog) -> Result<()> {
        let key = format!("{}:{}", log.timestamp, log.request_id);
        let value = serde_json::to_vec(log)?;
        self.journal_tree.insert(key.as_bytes(), value)?;
        self.journal_tree.flush()?;
        Ok(())
    }

    /// [Command Implementation] 통계 증가
    pub fn increment_op_count(&self, op_name: &str) -> Result<u64> {
        let key = format!("op_count:{}", op_name);
        let new_count = self.stats_tree.update_and_fetch(key.as_bytes(), |old| {
            let current = old.and_then(|b| b.try_into().ok().map(u64::from_le_bytes)).unwrap_or(0);
            Some((current + 1).to_le_bytes().to_vec())
        })?.map(|b| u64::from_le_bytes(b.as_ref().try_into().unwrap())).unwrap_or(1);
        
        self.stats_tree.flush()?;
        Ok(new_count)
    }

    /// [Query Implementation] 통계 조회
    pub fn recover_op_count(&self, op_name: &str) -> Result<u64> {
        let key = format!("op_count:{}", op_name);
        Ok(self.stats_tree.get(key.as_bytes())?
            .and_then(|b| b.as_ref().try_into().ok().map(u64::from_le_bytes))
            .unwrap_or(0))
    }

    /// Get total journal entries
    pub fn journal_count(&self) -> usize {
        self.journal_tree.len()
    }
}