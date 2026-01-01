# Krepis Sovereign Kernel Host v2.0.0

## Architecture Overview

The Krepis Kernel is a **Rust-controlled runtime host** that embeds Deno as an execution plane, not a framework. Rust maintains complete sovereignty over:

- Context lifecycle
- Permission system
- File system access
- Network operations
- Memory management

## Key Concepts

### 1. Control vs Execution Plane Separation

```
┌─────────────────────────────────────┐
│   Rust Control Plane (Sovereign)    │
│  - Context Creation                 │
│  - Permission Enforcement           │
│  - Resource Management              │
│  - Protobuf Serialization           │
└─────────────┬───────────────────────┘
              │ Op System (Zero-copy)
              ↓
┌─────────────────────────────────────┐
│  JavaScript Execution Plane (Deno)  │
│  - Business Logic                   │
│  - Explicit Context Usage           │
│  - Rust-provided Ops only           │
└─────────────────────────────────────┘
```

### 2. Explicit Context Propagation

Every JavaScript execution receives a Protobuf-serialized context:

```rust
// Rust creates and serializes
let ctx = KrepisContext {
    request_id: uuid::new_v4(),
    is_turbo_mode: true,
    priority: 10,
    // ...
};
```

```javascript
// JS receives via op
const ctxBuffer = Deno.core.ops.op_get_context();
// All operations must use this context
```

### 3. Op System (Rust-JS Bridge)

Operations are **Rust functions** exposed to JavaScript:

- `op_get_context()`: Retrieve serialized Protobuf context
- `op_log_from_js()`: Controlled logging to Rust tracing
- `op_check_permission()`: Permission validation (Rust decides)
- `op_increment_stats()`: Sovereign metrics tracking

## Building

```bash
# Build kernel with embedded Deno
cargo build --package krepis-kernel

# Run sovereign host
cargo run --package krepis-kernel

# Run tests
cargo test --package krepis-kernel
```

## Expected Output

```
🚀 Krepis Sovereign Kernel Host v2.0.0
⚡ Initializing Rust Control Plane...
✅ Context created: RequestID=<uuid>
🔒 Turbo Mode: true
📊 Priority Level: 10
🎯 Deno Isolate spawned - Rust maintains sovereignty
🔷 JavaScript Execution Plane Active
[JS] JS Runtime initialized
📦 Context received from Rust: <bytes> bytes
🔒 Read permission for /tmp/krepis/: true
🔒 Write permission (denied): false
[JS] Sovereign execution complete
✅ JavaScript bootstrap executed
📊 JS Ops Called: 1
🎉 Sovereign Kernel Host operational
```

## Security Model

### Default Deny

All operations are **denied by default**. JavaScript can only:

1. Call explicitly provided Rust ops
2. Access whitelisted paths (e.g., `/tmp/krepis/*`)
3. Use Rust-injected context

### No Implicit State

- No AsyncLocalStorage
- No global mutable state
- All context flows through Rust

## Performance Characteristics

- **Zero-copy FFI**: Shared memory for context propagation
- **Protobuf serialization**: Efficient binary encoding
- **Single-threaded JS**: Predictable execution model
- **Rust-controlled I/O**: All async operations intercepted

## Development Guidelines

### Adding New Ops

1. Define op in `src/ops.rs`:
```rust
#[op2]
pub fn op_my_operation(#[state] ctx: &Rc<Vec<u8>>) -> String {
    // Implementation
}
```

2. Register in extension:
```rust
ops: std::borrow::Cow::Borrowed(&[
    ops::op_my_operation::DECL,
]),
```

3. Call from JS:
```javascript
Deno.core.ops.op_my_operation();
```

### Context Usage

Always retrieve context at the start of JS execution:

```javascript
const ctxBuffer = Deno.core.ops.op_get_context();
// Decode with protobuf.js in production
```

## Architecture Compliance

This implementation follows:

- **Spec-001**: Explicit Context injection
- **Spec-004**: Rust sovereign control
- **Spec-003**: Zero-copy communication

## Roadmap

- [ ] Full Protobuf.js integration
- [ ] Multi-isolate support
- [ ] Advanced permission policies
- [ ] Hyper integration for HTTP
- [ ] KNUL protocol binding