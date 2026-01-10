//! Integration Tests - The Zero-cost Razor Final Assembly
//!
//! These tests verify that all components (Clock, Memory, Simulator) work
//! together seamlessly with zero runtime overhead.

use krepis_twin::domain::*;
use krepis_twin::domain::clock::{TimeMode, VirtualClock};
use krepis_twin::domain::memory::{MemoryConfig, SimulatedMemory};

// Production mode tests
mod production_tests {
    use super::*;
    use krepis_twin::domain::clock::ProductionBackend as ProdClockBackend;
    use krepis_twin::domain::memory::ProductionBackend as ProdMemBackend;

    #[test]
    fn test_store_buffer_visibility() {
        let mem_backend = ProdMemBackend::new(2, 2);
        let clock_backend = ProdClockBackend::new();
        let clock = VirtualClock::new(clock_backend, TimeMode::EventDriven);
        let memory = SimulatedMemory::new(mem_backend, clock, MemoryConfig::default());
        
        let mut sim = Simulator::new(memory);

        // Core 0 writes to address 42
        sim.memory_mut().write(0, 42, 999).unwrap();

        // Local forwarding: Core 0 sees its own write
        assert_eq!(sim.memory().read(0, 42), 999);

        // Core 1 doesn't see it yet (buffered)
        assert_eq!(sim.memory().read(1, 42), 0);

        // Process sync event
        assert!(sim.step());

        // Now Core 1 can see it (flushed to main memory)
        assert_eq!(sim.memory().read(1, 42), 999);
    }

    #[test]
    fn test_litmus_store_buffering() {
        // Classic "Store Buffering" litmus test for relaxed memory
        let mem_backend = ProdMemBackend::new(2, 2);
        let clock_backend = ProdClockBackend::new();
        let clock = VirtualClock::new(clock_backend, TimeMode::EventDriven);
        let memory = SimulatedMemory::new(mem_backend, clock, MemoryConfig::default());
        
        let mut sim = Simulator::new(memory);

        // Core 0: x = 1
        sim.memory_mut().write(0, 100, 1).unwrap();
        
        // Core 1: y = 1
        sim.memory_mut().write(1, 200, 1).unwrap();

        // Before flush: each core sees only its own write
        assert_eq!(sim.memory().read(0, 100), 1);
        assert_eq!(sim.memory().read(0, 200), 0);
        assert_eq!(sim.memory().read(1, 100), 0);
        assert_eq!(sim.memory().read(1, 200), 1);

        // Process all events
        sim.run_until_idle();

        // After flush: both cores see both writes
        assert_eq!(sim.memory().read(0, 100), 1);
        assert_eq!(sim.memory().read(0, 200), 1);
        assert_eq!(sim.memory().read(1, 100), 1);
        assert_eq!(sim.memory().read(1, 200), 1);
    }

    #[test]
    fn test_fence_ensures_ordering() {
        let mem_backend = ProdMemBackend::new(2, 4); // 버퍼 크기를 넉넉히 4로 조정
        let clock_backend = ProdClockBackend::new();
        let clock = VirtualClock::new(clock_backend, TimeMode::EventDriven);
        let memory = SimulatedMemory::new(mem_backend, clock, MemoryConfig::default());
        
        let mut sim = Simulator::new(memory);

        sim.memory_mut().write(0, 10, 100).unwrap();
        sim.memory_mut().write(0, 20, 200).unwrap();
        sim.memory_mut().fence(0).unwrap(); 
        
        // Fence 이벤트가 처리되어 버퍼가 비워지도록 한 번 소모합니다.
        sim.step(); 

        sim.memory_mut().write(0, 30, 300).unwrap();
        sim.run_until_idle();

        assert_eq!(sim.memory().read_main_memory(10), 100);
        assert_eq!(sim.memory().read_main_memory(20), 200);
        assert_eq!(sim.memory().read_main_memory(30), 300);
    }

    #[test]
    fn test_time_ordering_preserved() {
        let mem_backend = ProdMemBackend::new(2, 2);
        let clock_backend = ProdClockBackend::new();
        let clock = VirtualClock::new(clock_backend, TimeMode::EventDriven);
        let memory = SimulatedMemory::new(mem_backend, clock, MemoryConfig::default());
        
        let mut sim = Simulator::new(memory);

        // Multiple writes to same address
        sim.memory_mut().write(0, 42, 100).unwrap();
        sim.memory_mut().write(0, 42, 200).unwrap();

        // Process in order
        sim.step();
        assert_eq!(sim.memory().read_main_memory(42), 100);

        sim.step();
        assert_eq!(sim.memory().read_main_memory(42), 200);
    }

    #[test]
    fn test_builder_pattern() {
        let mut sim = ProductionSimulatorBuilder::new()
            .num_cores(16)
            .buffer_size(8)
            .build();

        sim.memory_mut().write(0, 1000, 42).unwrap();
        sim.run_until_idle();
        assert_eq!(sim.memory().read_main_memory(1000), 42);
    }
}

// Verification mode tests
mod verification_tests {
    use super::*;
    use krepis_twin::domain::clock::VerificationBackend as VerifClockBackend;
    use krepis_twin::domain::memory::VerificationBackend as VerifMemBackend;

    #[test]
    fn test_verification_store_buffer() {
        let mem_backend = VerifMemBackend::new();
        let clock_backend = VerifClockBackend::new();
        let clock = VirtualClock::new(clock_backend, TimeMode::EventDriven);
        let memory = SimulatedMemory::new(mem_backend, clock, MemoryConfig::default());
        
        let mut sim = Simulator::new(memory);

        // Core 0 writes
        sim.memory_mut().write(0, 0, 999).unwrap();

        // Local forwarding works
        assert_eq!(sim.memory().read(0, 0), 999);
        assert_eq!(sim.memory().read(1, 0), 0);

        // Process event
        sim.step();

        // Now visible to all cores
        assert_eq!(sim.memory().read(1, 0), 999);
    }

    #[test]
    fn test_verification_litmus_test() {
        let mem_backend = VerifMemBackend::new();
        let clock_backend = VerifClockBackend::new();
        let clock = VirtualClock::new(clock_backend, TimeMode::EventDriven);
        let memory = SimulatedMemory::new(mem_backend, clock, MemoryConfig::default());
        
        let mut sim = Simulator::new(memory);

        // Store buffering litmus test
        sim.memory_mut().write(0, 0, 1).unwrap();
        sim.memory_mut().write(1, 1, 1).unwrap();

        // Before flush: isolation
        assert_eq!(sim.memory().read(0, 0), 1);
        assert_eq!(sim.memory().read(0, 1), 0);
        assert_eq!(sim.memory().read(1, 0), 0);
        assert_eq!(sim.memory().read(1, 1), 1);

        // After flush: global visibility
        sim.run_until_idle();

        assert_eq!(sim.memory().read(0, 0), 1);
        assert_eq!(sim.memory().read(0, 1), 1);
        assert_eq!(sim.memory().read(1, 0), 1);
        assert_eq!(sim.memory().read(1, 1), 1);
    }

    #[test]
    fn test_verification_builder() {
        let mut sim = VerificationSimulatorBuilder::build();

        sim.memory_mut().write(0, 0, 42).unwrap();
        sim.run_until_idle();
        assert_eq!(sim.memory().read_main_memory(0), 42);
    }

    #[test]
    fn test_verification_bounds() {
        let mut sim = VerificationSimulatorBuilder::build();

        // Fill buffer
        sim.memory_mut().write(0, 0, 100).unwrap();
        sim.memory_mut().write(0, 1, 200).unwrap();

        // Third write should fail (buffer full)
        assert!(sim.memory_mut().write(0, 2, 300).is_err());
    }
}

// Type alias tests
#[test]
fn test_production_simulator_alias() {
    let mem_backend = memory::ProductionBackend::new(2, 2);
    let clock_backend = clock::ProductionBackend::new();
    let clock = VirtualClock::new(clock_backend, TimeMode::EventDriven);
    let memory = SimulatedMemory::new(mem_backend, clock, MemoryConfig::default());
    
    let mut sim: ProductionSimulator = Simulator::new(memory);
    
    sim.memory_mut().write(0, 100, 42).unwrap();
    sim.run_until_idle();
    assert_eq!(sim.memory().read_main_memory(100), 42);
}

#[test]
fn test_verification_simulator_alias() {
    let mem_backend = memory::VerificationBackend::new();
    let clock_backend = clock::VerificationBackend::new();
    let clock = VirtualClock::new(clock_backend, TimeMode::EventDriven);
    let memory = SimulatedMemory::new(mem_backend, clock, MemoryConfig::default());
    
    let mut sim: VerificationSimulator = Simulator::new(memory);
    
    sim.memory_mut().write(0, 0, 42).unwrap();
    sim.run_until_idle();
    assert_eq!(sim.memory().read_main_memory(0), 42);
}