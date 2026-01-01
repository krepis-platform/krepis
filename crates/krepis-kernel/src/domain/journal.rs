use serde::{Deserialize, Serialize};

/// [Domain] Transaction Log Entry (Pure Data)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TransactionLog {
    pub timestamp: i64,
    pub op_name: String,
    pub request_id: String,
    pub status: LogStatus,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum LogStatus {
    Started,
    Completed,
    Failed,
}