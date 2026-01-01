use deno_core::{JsRuntime, RuntimeOptions};
use std::rc::Rc;

mod proto {
    include!(concat!(env!("OUT_DIR"), "/krepis.core.rs"));
}

// Import ops module for testing
#[path = "../src/ops.rs"]
mod ops;

use proto::KrepisContext;
use prost::Message;

#[tokio::test]
async fn test_sovereign_runtime_creation() {
    let ctx = KrepisContext {
        request_id: "test-001".to_string(),
        tenant_id: "test-tenant".to_string(),
        priority: 5,
        is_turbo_mode: false,
        trace_id: "trace-001".to_string(),
        timestamp: 1234567890,
        metadata: Default::default(),
    };

    let ctx_buffer = Rc::new(ctx.encode_to_vec());
    
    let ext = deno_core::Extension {
        name: "krepis_test",
        ops: std::borrow::Cow::Borrowed(&[ops::op_get_context::DECL]),
        op_state_fn: Some(Box::new(move |state| {
            state.put(ctx_buffer.clone());
        })),
        ..Default::default()
    };

    let mut runtime = JsRuntime::new(RuntimeOptions {
        extensions: vec![ext],
        ..Default::default()
    });

    let result = runtime.execute_script(
        "test",
        r#"
            const buffer = Deno.core.ops.op_get_context();
            buffer.length > 0;
        "#,
    );

    assert!(result.is_ok());
}

#[tokio::test]
async fn test_permission_system() {
    let ctx_buffer = Rc::new(vec![]);
    
    let ext = deno_core::Extension {
        name: "krepis_test",
        ops: std::borrow::Cow::Borrowed(&[
            ops::op_check_permission::DECL,
        ]),
        op_state_fn: Some(Box::new(move |state| {
            state.put(ctx_buffer.clone());
        })),
        ..Default::default()
    };

    let mut runtime = JsRuntime::new(RuntimeOptions {
        extensions: vec![ext],
        ..Default::default()
    });

    let result = runtime.execute_script(
        "permission_test",
        r#"
            const allowed = Deno.core.ops.op_check_permission("read", "/tmp/krepis/test");
            const denied = Deno.core.ops.op_check_permission("write", "/etc/passwd");
            
            allowed === true && denied === false;
        "#,
    );

    assert!(result.is_ok());
}

#[test]
fn test_protobuf_context_creation() {
    let ctx = KrepisContext {
        request_id: "proto-test".to_string(),
        tenant_id: "tenant-proto".to_string(),
        priority: 10,
        is_turbo_mode: true,
        trace_id: "trace-proto".to_string(),
        timestamp: 1234567890,
        metadata: Default::default(),
    };

    let encoded = ctx.encode_to_vec();
    let decoded = KrepisContext::decode(&encoded[..]).unwrap();

    assert_eq!(decoded.request_id, "proto-test");
    assert_eq!(decoded.is_turbo_mode, true);
    assert_eq!(decoded.priority, 10);
}