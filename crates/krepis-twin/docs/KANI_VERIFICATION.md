# Kani Formal Verification

## Setup

```bash
# Install Kani
cargo install --locked kani-verifier
cargo kani setup
```

## Running Proofs

```bash
# Verify all proofs
cargo kani --features verification

# Verify specific module
cargo kani --features verification --harness proof_memory_safety
cargo kani --features verification --harness proof_time_monotonic

# With increased unwinding (if needed)
cargo kani --features verification --unwind 8
```

## Proofs Included

### VirtualClock (T-001, T-002, T-003)
- `proof_time_monotonic`: Time never decreases
- `proof_lamport_increments`: Lamport clock increments
- `proof_event_ordering`: Events fire in time order
- `proof_bounded_limits`: Queue/time limits enforced

### SimulatedMemory (M-001, M-002, M-003)
- `proof_memory_safety`: No panics or UB
- `proof_buffer_isolation`: Local forwarding works
- `proof_flush_visibility`: Flush makes writes global
- `proof_bounded_buffer`: Buffer size limits enforced
- `proof_fifo_ordering`: Writes flush in FIFO order

## Constraints

All proofs use bounded model checking:
- Max cores: 2
- Max buffer size: 2
- Max address space: 4
- Max unwinding: 4

## Expected Runtime

- Clock proofs: ~30 seconds each
- Memory proofs: ~60 seconds each
- Total: ~5-10 minutes