//! Kani Formal Verification Proofs - The Zero-cost Razor Edition
//!
//! # Victory Report: Kani Finally Says "SUCCESS"
//!
//! Previous battle (lost):
//! ```text
//! SimulatedMemory { Arc<DashMap>, Vec<RwLock> }
//!     ↓
//! Kani: "syscall? malloc? PANIC!" 💥
//!     ↓
//! VERIFICATION FAILED ❌
//! ```
//!
//! Current battle (won):
//! ```text
//! SimulatedMemory<VerificationBackend, VerifClockBackend>
//!     ↓
//! VerificationBackend { [Value; 4], [RefCell; 2] } ← Stack only!
//!     ↓
//! Kani: "I can prove this mathematically!" ✅
//!     ↓
//! VERIFICATION SUCCESSFUL 🎉
//! ```

#[cfg(kani)]
mod kani_proofs {
    use super::super::*;
    use crate::domain::clock::{TimeMode, VerificationBackend as VerifClockBackend, VirtualClock};

   #[kani::proof]
    #[kani::unwind(4)]
    fn proof_memory_safety() {
        let mem_backend = VerificationBackend::new();
        let clock_backend = VerifClockBackend::new();
        let clock = VirtualClock::new(clock_backend, TimeMode::EventDriven);
        
        let config = MemoryConfig {
            num_cores: 2,
            max_buffer_size: 2,
            consistency_model: ConsistencyModel::Relaxed,
            initial_size: 2,
        };
        let mut mem = SimulatedMemory::new(mem_backend, clock, config);

        let core: usize = kani::any();
        let addr: usize = 0;
        let val: u64 = kani::any();

        kani::assume(core < 2);

        let _ = mem.read(core, addr);

        if mem.get_buffer_len(core) < 2 {
            let result = mem.write(core, addr, val);
            kani::assert(result.is_ok(), "Write should succeed when buffer not full");
        }
        std::mem::forget(mem); 
    }

    #[kani::proof]
    #[kani::unwind(16)]
    fn proof_buffer_isolation() {
        let mem_backend = VerificationBackend::new();
        let clock_backend = VerifClockBackend::new();
        let clock = VirtualClock::new(clock_backend, TimeMode::EventDriven);
        let config = MemoryConfig {
            num_cores: 2,
            max_buffer_size: 2,
            consistency_model: ConsistencyModel::Relaxed,
            initial_size: 4,
        };
        let mut mem = SimulatedMemory::new(mem_backend, clock, config);

        let addr: usize = kani::any();
        let val: u64 = kani::any();
        kani::assume(addr < 4);
        kani::assume(val > 0);

        let write_result = mem.write(0, addr, val);
        kani::assume(write_result.is_ok());

        let read_val = mem.read(0, addr);
        kani::assert(read_val == val, "Core must see its own buffered write");

        let other_val = mem.read(1, addr);
        kani::assert(other_val == 0, "Other core must not see buffered write");
    }

    #[kani::proof]
    #[kani::unwind(16)]
    fn proof_flush_visibility() {
        let mem_backend = VerificationBackend::new();
        let clock_backend = VerifClockBackend::new();
        let clock = VirtualClock::new(clock_backend, TimeMode::EventDriven);
        let config = MemoryConfig {
            num_cores: 2,
            max_buffer_size: 2,
            consistency_model: ConsistencyModel::Relaxed,
            initial_size: 4,
        };
        let mut mem = SimulatedMemory::new(mem_backend, clock, config);

        let addr: usize = kani::any();
        let val: u64 = kani::any();
        kani::assume(addr < 4);
        kani::assume(val > 0);

        let write_result = mem.write(0, addr, val);
        kani::assume(write_result.is_ok());
        
        let flush_result = mem.flush_one(0);
        kani::assume(flush_result.is_ok());

        let main_val = mem.read_main_memory(addr);
        kani::assert(main_val == val, "Flush must update main memory");

        for core in 0..2 {
            let read_val = mem.read(core, addr);
            kani::assert(read_val == val, "All cores must see flushed write");
        }
    }

    #[kani::proof]
    #[kani::unwind(16)]
    fn proof_bounded_buffer() {
        let mem_backend = VerificationBackend::new();
        let clock_backend = VerifClockBackend::new();
        let clock = VirtualClock::new(clock_backend, TimeMode::EventDriven);
        let config = MemoryConfig {
            num_cores: 2,
            max_buffer_size: 2,
            consistency_model: ConsistencyModel::Relaxed,
            initial_size: 4,
        };
        let mut mem = SimulatedMemory::new(mem_backend, clock, config);

        let _ = mem.write(0, 0, 1);
        let _ = mem.write(0, 1, 2);
        let result = mem.write(0, 2, 3);

        kani::assert(result.is_err(), "Buffer overflow must be prevented");
        kani::assert(mem.get_buffer_len(0) <= 2, "Buffer size must respect limit");
    }

    #[kani::proof]
    #[kani::unwind(16)]
    fn proof_fifo_ordering() {
        let mem_backend = VerificationBackend::new();
        let clock_backend = VerifClockBackend::new();
        let clock = VirtualClock::new(clock_backend, TimeMode::EventDriven);
        let config = MemoryConfig {
            num_cores: 2,
            max_buffer_size: 2,
            consistency_model: ConsistencyModel::Relaxed,
            initial_size: 4,
        };
        let mut mem = SimulatedMemory::new(mem_backend, clock, config);

        let addr = 0usize;
        kani::assume(mem.write(0, addr, 100).is_ok());
        kani::assume(mem.write(0, addr, 200).is_ok());

        kani::assume(mem.flush_one(0).is_ok());
        kani::assert(mem.read_main_memory(addr) == 100, "First write must flush first");

        kani::assume(mem.flush_one(0).is_ok());
        kani::assert(mem.read_main_memory(addr) == 200, "Second write must flush second");
    }
}