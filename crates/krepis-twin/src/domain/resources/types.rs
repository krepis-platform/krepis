//! Core Types for Resource Tracking

use std::fmt;

/// Thread identifier (maps to TLA+ Threads)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ThreadId(pub usize);

impl ThreadId {
    /// Create a new thread identifier
    #[inline(always)]
    pub const fn new(id: usize) -> Self {
        Self(id)
    }

    /// Get the underlying usize value
    #[inline(always)]
    pub const fn as_usize(self) -> usize {
        self.0
    }
}

impl fmt::Display for ThreadId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "t{}", self.0)
    }
}

/// Resource identifier (maps to TLA+ Resources)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ResourceId(pub usize);

impl ResourceId {
    /// Create a new resource identifier
    #[inline(always)]
    pub const fn new(id: usize) -> Self {
        Self(id)
    }

    /// Get the underlying usize value
    #[inline(always)]
    pub const fn as_usize(self) -> usize {
        self.0
    }
}

impl fmt::Display for ResourceId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "r{}", self.0)
    }
}

/// Resource type (maps to TLA+ ResourceTypes)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResourceType {
    /// Binary lock (TLA+ Mutex)
    Mutex,
    /// Counting lock (TLA+ Semaphore)
    Semaphore {
        /// Maximum number of permits available 
        max_permits: usize 
    },
}

/// Thread status (maps to TLA+ ThreadStatusValues)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ThreadStatus {
    /// Thread is running
    Running,
    /// Thread is blocked on a resource
    Blocked,
    /// Thread has finished
    Finished,
}

/// Error types
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResourceError {
    /// Thread ID out of bounds
    InvalidThreadId(ThreadId),
    
    /// Resource ID out of bounds
    InvalidResourceId(ResourceId),
    
    /// Thread tried to acquire resource it already owns (self-deadlock)
    AlreadyOwned {
        /// The thread that attempted to re-acquire
        thread: ThreadId,
        /// The resource already owned
        resource: ResourceId,
    },
    
    /// Thread tried to release resource it doesn't own
    NotOwned {
        /// The thread that attempted to release
        thread: ThreadId,
        /// The resource not owned
        resource: ResourceId,
    },
    
    /// Deadlock detected (cycle in wait-for graph)
    DeadlockDetected {
        /// The cycle of threads involved in the deadlock
        cycle: Vec<ThreadId>,
    },
    
    /// Thread finished while still holding resources
    ResourceLeak {
        /// The thread that finished
        thread: ThreadId,
        /// Resources still held
        held_resources: Vec<ResourceId>,
    },
}

impl fmt::Display for ResourceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidThreadId(t) => write!(f, "Invalid thread ID: {}", t),
            Self::InvalidResourceId(r) => write!(f, "Invalid resource ID: {}", r),
            Self::AlreadyOwned { thread, resource } => {
                write!(f, "Thread {} already owns resource {}", thread, resource)
            }
            Self::NotOwned { thread, resource } => {
                write!(f, "Thread {} does not own resource {}", thread, resource)
            }
            Self::DeadlockDetected { cycle } => {
                write!(f, "Deadlock detected! Cycle: ")?;
                for (i, t) in cycle.iter().enumerate() {
                    if i > 0 {
                        write!(f, " -> ")?;
                    }
                    write!(f, "{}", t)?;
                }
                Ok(())
            }
            Self::ResourceLeak { thread, held_resources } => {
                write!(f, "Thread {} finished with resources: ", thread)?;
                for (i, r) in held_resources.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", r)?;
                }
                Ok(())
            }
        }
    }
}

impl std::error::Error for ResourceError {}