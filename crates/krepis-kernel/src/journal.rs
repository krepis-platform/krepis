use anyhow::{Context, Result};
use serde::{Deserialize, Serialize};
use sled::Db;
use std::path::Path;
use std::sync::Arc;
use tracing::{info, warn};

/// Transaction Log Entry
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TransactionLog {
    pub timestamp: i64,
    pub op_name: String,
    pub request_id: String,
    pub status: LogStatus,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum LogStatus {
    Started,
    Completed,
    Failed,
}

/// Sovereign Journal System
/// Provides atomic, persistent logging for all kernel operations
pub struct SovereignJournal {
    db: Arc<Db>,
    journal_tree: sled::Tree,
    stats_tree: sled::Tree,
}

impl SovereignJournal {
    /// Initialize journal at given path
    pub fn new<P: AsRef<Path>>(path: P) -> Result<Self> {
        let db = sled::open(path.as_ref())
            .context("Failed to open Sled database")?;
        
        let journal_tree = db.open_tree("journal")
            .context("Failed to open journal tree")?;
        
        let stats_tree = db.open_tree("stats")
            .context("Failed to open stats tree")?;
        
        info!("📚 Sovereign Journal initialized at {:?}", path.as_ref());
        
        Ok(Self {
            db: Arc::new(db),
            journal_tree,
            stats_tree,
        })
    }

    /// Log a transaction atomically
    pub fn log_transaction(&self, log: &TransactionLog) -> Result<()> {
        let key = format!("{}:{}", log.timestamp, log.request_id);
        let value = serde_json::to_vec(log)
            .context("Failed to serialize transaction log")?;
        
        self.journal_tree.insert(key.as_bytes(), value)
            .context("Failed to insert journal entry")?;
        
        // Ensure durability
        self.journal_tree.flush()
            .context("Failed to flush journal")?;
        
        Ok(())
    }

    /// Increment and persist operation counter
    pub fn increment_op_count(&self, op_name: &str) -> Result<u64> {
        let key = format!("op_count:{}", op_name);
        
        let new_count = self.stats_tree
            .update_and_fetch(key.as_bytes(), |old_value| {
                let current = old_value
                    .and_then(|bytes| {
                        let arr: [u8; 8] = bytes.try_into().ok()?;
                        Some(u64::from_le_bytes(arr))
                    })
                    .unwrap_or(0);
                
                Some((current + 1).to_le_bytes().to_vec())
            })
            .context("Failed to increment op count")?
            .map(|bytes| {
                let arr: [u8; 8] = bytes.as_ref().try_into().unwrap();
                u64::from_le_bytes(arr)
            })
            .unwrap_or(1);
        
        // Ensure durability
        self.stats_tree.flush()
            .context("Failed to flush stats")?;
        
        Ok(new_count)
    }

    /// Recover operation count from persistent storage
    pub fn recover_op_count(&self, op_name: &str) -> Result<u64> {
        let key = format!("op_count:{}", op_name);
        
        let count = self.stats_tree
            .get(key.as_bytes())
            .context("Failed to read op count")?
            .and_then(|bytes| {
                let arr: [u8; 8] = bytes.as_ref().try_into().ok()?;
                Some(u64::from_le_bytes(arr))
            })
            .unwrap_or(0);
        
        if count > 0 {
            info!("🔄 Recovered {} count: {}", op_name, count);
        }
        
        Ok(count)
    }

    /// Get total journal entries
    pub fn journal_count(&self) -> usize {
        self.journal_tree.len()
    }

    /// Clear all journal data (for testing)
    pub fn clear_all(&self) -> Result<()> {
        warn!("⚠️  Clearing all journal data");
        self.journal_tree.clear()
            .context("Failed to clear journal")?;
        self.stats_tree.clear()
            .context("Failed to clear stats")?;
        self.db.flush()
            .context("Failed to flush database")?;
        Ok(())
    }

    /// Get recent journal entries
    pub fn get_recent_logs(&self, limit: usize) -> Result<Vec<TransactionLog>> {
        let mut logs = Vec::new();
        
        for result in self.journal_tree.iter().rev().take(limit) {
            let (_, value) = result.context("Failed to iterate journal")?;
            let log: TransactionLog = serde_json::from_slice(&value)
                .context("Failed to deserialize log entry")?;
            logs.push(log);
        }
        
        Ok(logs)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::SystemTime;

    #[test]
    fn test_journal_creation() {
        let temp_dir = tempfile::tempdir().unwrap();
        let journal = SovereignJournal::new(temp_dir.path()).unwrap();
        assert_eq!(journal.journal_count(), 0);
    }

    #[test]
    fn test_transaction_logging() {
        let temp_dir = tempfile::tempdir().unwrap();
        let journal = SovereignJournal::new(temp_dir.path()).unwrap();
        
        let log = TransactionLog {
            timestamp: SystemTime::now()
                .duration_since(SystemTime::UNIX_EPOCH)
                .unwrap()
                .as_millis() as i64,
            op_name: "test_op".to_string(),
            request_id: "req-001".to_string(),
            status: LogStatus::Completed,
        };
        
        journal.log_transaction(&log).unwrap();
        assert_eq!(journal.journal_count(), 1);
    }

    #[test]
    fn test_op_count_persistence() {
        let temp_dir = tempfile::tempdir().unwrap();
        let journal = SovereignJournal::new(temp_dir.path()).unwrap();
        
        // Increment
        let count1 = journal.increment_op_count("test_op").unwrap();
        assert_eq!(count1, 1);
        
        let count2 = journal.increment_op_count("test_op").unwrap();
        assert_eq!(count2, 2);
        
        // Recover
        let recovered = journal.recover_op_count("test_op").unwrap();
        assert_eq!(recovered, 2);
    }
}