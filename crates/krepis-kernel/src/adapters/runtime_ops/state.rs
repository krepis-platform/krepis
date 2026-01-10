/// Sovereign Stats - track JS execution metrics
#[derive(Default, Debug)]
pub struct SovereignStats {
    pub js_ops_called: u64,
    pub contexts_created: u64,
}