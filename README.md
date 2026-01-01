# Krepis: Sovereign AI-Native ADaaS Platform

> Architecture Development as a Service - v2.0.0 (The Sovereign Kernel)

## 🎯 Core Philosophy

**Sovereign Control, Fractal Intelligence**

- **Systemic Rigidity**: Rust + Deno for deterministic runtime
- **Fractal Intelligence**: Master-Expert-Sub AI legion architecture
- **Explicit Context**: Zero implicit state propagation
- **Sovereign Kernel**: Rust controls Deno, not vice versa

## 🏗️ Architecture Overview

### Hybrid Sovereign Monorepo

```
krepis/
├── Cargo.toml              # Rust workspace root
├── deno.json               # Deno runtime config
├── crates/
│   ├── krepis-kernel/      # 🆕 Sovereign Kernel Host (Rust embeds Deno)
│   │   ├── src/
│   │   │   ├── main.rs     # Tokio async kernel
│   │   │   ├── lib.rs      # FFI exports
│   │   │   └── ops.rs      # Rust-JS bridge operations
│   │   ├── proto/          # Protobuf schemas
│   │   └── tests/          # Integration tests
│   └── krepis-knul/        # KNUL protocol engine (Rust library)
└── packages/
    ├── cli/                # Sovereign Master CLI (Rust binary)
    └── core/               # Trinity Framework Core (TypeScript/Deno)
        └── src/native/     # FFI bindings for Rust
```

## 🚀 Quick Start

### Prerequisites

- Rust 1.75+ (latest stable)
- Cargo
- Git

### Build & Run Sovereign Kernel

```bash
# Clone repository
git clone https://github.com/krepis/krepis.git
cd krepis

# Build Sovereign Kernel
./scripts/build-sovereign.sh

# Run demo
./scripts/demo-sovereign.sh

# Or manually
cargo run --package krepis-kernel
```

### Expected Output

```
🚀 Krepis Sovereign Kernel Host v2.0.0
⚡ Initializing Rust Control Plane...
✅ Context created: RequestID=<uuid>
🔒 Turbo Mode: true
🎯 Deno Isolate spawned - Rust maintains sovereignty
🔷 JavaScript Execution Plane Active
📦 Context received from Rust: <bytes> bytes
🔒 Read permission for /tmp/krepis/: true
✅ JavaScript bootstrap executed
🎉 Sovereign Kernel Host operational
```

## 📐 Architecture Principles

### 1. Control Plane vs Execution Plane

```
┌────────────────────────────┐
│   Rust Control Plane       │  ← Owns context, permissions, I/O
│   (Sovereign Authority)    │
└──────────┬─────────────────┘
           │ Op System
           ↓
┌────────────────────────────┐
│   Deno Execution Plane     │  ← Runs JS, uses Rust-provided ops
│   (Controlled Worker)      │
└────────────────────────────┘
```

### 2. Explicit Context Propagation

Every operation receives Protobuf-serialized context:

```rust
// Rust creates
let ctx = KrepisContext {
    request_id: uuid::new_v4(),
    is_turbo_mode: true,
    priority: 10,
};
```

```javascript
// JS receives
const ctx = Deno.core.ops.op_get_context();
```

### 3. Trinity Pattern Enforcement

All business logic follows:

1. **Hexagonal Architecture**: Adapter isolation
2. **Functional Core**: Pure functions in domain layer
3. **CQS**: Command-Query Separation

## 🧪 Testing

### Rust Tests

```bash
cargo test --workspace
```

### Integration Tests

```bash
cargo test --package krepis-kernel --test sovereign_test
```

## 🔐 Security Model

- **Default Deny**: All operations denied unless explicitly allowed
- **Rust-Controlled I/O**: No direct file/network access from JS
- **Permission System**: `op_check_permission` validates every request
- **No Implicit State**: Zero global mutable state

## 📊 Key Features

- ✅ Rust embeds Deno (not Node.js)
- ✅ Zero-copy FFI via `deno_core`
- ✅ Protobuf context serialization
- ✅ Explicit permission system
- ✅ Sovereign metrics tracking
- ✅ Async/await in both Rust and JS

## 🛠️ Development

### Add New Operations

1. Define in `crates/krepis-kernel/src/ops.rs`
2. Register in extension
3. Call from JavaScript via `Deno.core.ops`

See `crates/krepis-kernel/SOVEREIGN.md` for details.

## 📝 License

Apache-2.0

## 🌐 Links

- Documentation: https://docs.krepis.dev
- Sovereign Kernel Guide: [SOVEREIGN.md](crates/krepis-kernel/SOVEREIGN.md)

---

**Status**: Phase 2 - Sovereign Kernel Host (v2.0.0) ✅