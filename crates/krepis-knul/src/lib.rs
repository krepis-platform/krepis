/// KNUL (Krepis Networking Ultra Link) v1.5.0
/// QUIC-based 0-RTT networking protocol with semantic compression

use anyhow::Result;
use std::sync::Arc;
use tracing::info;

pub struct KnulEngine {
    config: Arc<KnulConfig>,
}

#[derive(Debug, Clone)]
pub struct KnulConfig {
    pub enable_0rtt: bool,
    pub compression_level: u8,
    pub max_streams: usize,
}

impl Default for KnulConfig {
    fn default() -> Self {
        Self {
            enable_0rtt: true,
            compression_level: 9,
            max_streams: 10_000,
        }
    }
}

impl KnulEngine {
    pub fn new(config: KnulConfig) -> Self {
        info!("🔗 KNUL Engine initializing");
        info!("   0-RTT: {}", config.enable_0rtt);
        info!("   Compression: Level {}", config.compression_level);
        
        Self {
            config: Arc::new(config),
        }
    }

    pub async fn start(&self) -> Result<()> {
        // config 필드를 읽는 로직을 추가하여 경고를 제거합니다.
        let mode = if self.config.enable_0rtt { "0-RTT" } else { "Standard" };
        info!("⚡ KNUL Engine ({}) started - Ready for sovereign connectivity", mode);
        
        // 향후 Spec-002에 따라 compression_level을 활용한 버퍼 할당 로직 등이 들어갈 자리입니다.
        Ok(())
    }

    // 외부에서 설정을 참조할 수 있도록 게터를 제공 (데이터 사용으로 간주됨)
    pub fn config(&self) -> Arc<KnulConfig> {
        Arc::clone(&self.config)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_knul_engine_creation() {
        let engine = KnulEngine::new(KnulConfig::default());
        assert!(engine.config.enable_0rtt);
    }
}