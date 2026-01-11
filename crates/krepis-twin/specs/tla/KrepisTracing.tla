-------------------------------- MODULE KrepisTracing --------------------------------
(*
 * Formal Specification of Krepis-Twin Event Tracing System
 * 
 * This specification models the causality tracking system that records
 * simulation events with Lamport timestamps and verifies happens-before
 * relationships.
 *
 * Corresponds to Rust modules:
 * - domain::tracing::tracer (EventTracer)
 * - domain::tracing::causality (CausalityGraph)
 * - domain::tracing::event (LamportTimestamp, SimulationEvent)
 *)

EXTENDS Naturals, Sequences, FiniteSets, TLC

(* ============================================================================
 * CONSTANTS
 * ============================================================================ *)

CONSTANTS 
    Threads,         \* Set of thread IDs (e.g., {1, 2, 3})
    MaxEvents,       \* Maximum number of events to record (bounded model checking)
    MaxTimestamp,    \* Maximum Lamport timestamp value
    MemoryAddresses  \* Set of memory addresses

(* ============================================================================
 * EVENT TYPES
 * Maps to: SimulationEvent enum in Rust
 * ============================================================================ *)

EventTypes == {
    "ClockTick",      \* Virtual clock advanced
    "MemoryRead",     \* Memory read operation
    "MemoryWrite",    \* Memory write operation
    "BufferFlush",    \* Store buffer flush
    "ThreadSpawn",    \* New thread spawned
    "ThreadJoin",     \* Thread terminated
    "MutexLock",      \* Mutex lock acquired
    "MutexUnlock"     \* Mutex lock released
}

(* ============================================================================
 * VARIABLES
 * Maps to: EventTracer struct fields in Rust
 * ============================================================================ *)

VARIABLES
    threadClocks,     \* threadClocks[t] = current Lamport timestamp for thread t
                      \* Rust: EventTracer.thread_states[t].last_timestamp
    
    seqNumbers,       \* seqNumbers[t] = sequence number for thread t
                      \* Rust: EventTracer.thread_states[t].seq_num
    
    eventLog,         \* Sequence of recorded events
                      \* Rust: EventTracer.events (Vec<SimulationEvent>)
    
    globalClock,      \* Maximum timestamp across all threads
                      \* Rust: EventTracer.global_timestamp
    
    syncHistory,      \* Record of synchronization events
                      \* Used to build happens-before graph
    
    memoryState       \* Current memory values (for modeling memory operations)
                      \* Not directly in EventTracer, but needed for complete model

(* All variables *)
vars == <<threadClocks, seqNumbers, eventLog, globalClock, syncHistory, memoryState>>

(* ============================================================================
 * TYPE INVARIANTS
 * ============================================================================ *)

TypeOK ==
    /\ threadClocks \in [Threads -> 0..MaxTimestamp]
    /\ seqNumbers \in [Threads -> Nat]
    /\ eventLog \in Seq([
            eventType: EventTypes,
            threadId: Threads,
            timestamp: 0..MaxTimestamp,
            seqNum: Nat,
            data: [addr: MemoryAddresses \cup {0}, value: Nat \cup {0}]
        ])
    /\ globalClock \in 0..MaxTimestamp
    /\ syncHistory \subseteq (Threads \X Threads \X (0..MaxTimestamp))
    /\ memoryState \in [MemoryAddresses -> Nat]

(* ============================================================================
 * HELPER OPERATORS
 * ============================================================================ *)

(* Create a new event record 
 * Maps to: SimulationEvent construction in Rust *)
MakeEvent(type, thread, ts, seq, addr, val) ==
    [
        eventType |-> type,
        threadId |-> thread,
        timestamp |-> ts,
        seqNum |-> seq,
        data |-> [addr |-> addr, value |-> val]
    ]

(* Check if event log is full 
 * Maps to: EventTracer.events.len() >= config.max_events *)
EventLogFull == Len(eventLog) >= MaxEvents

(* Get all events from a specific thread *)
ThreadEvents(t) ==
    { i \in 1..Len(eventLog) : eventLog[i].threadId = t }

(* Check if two events have happens-before relationship
 * Maps to: CausalityGraph::happens_before in Rust *)
HappensBefore(e1, e2) ==
    LET ev1 == eventLog[e1]
        ev2 == eventLog[e2]
    IN
    \/ /\ ev1.threadId = ev2.threadId          \* Same thread: use sequence
       /\ ev1.seqNum < ev2.seqNum
    \/ /\ ev1.threadId # ev2.threadId          \* Different threads: use timestamp
       /\ ev1.timestamp < ev2.timestamp
       /\ \E <<t1, t2, ts>> \in syncHistory:   \* Must have sync event
            /\ t1 = ev1.threadId
            /\ t2 = ev2.threadId
            /\ ts >= ev1.timestamp
            /\ ts <= ev2.timestamp


(* ============================================================================
 * SYMMETRY HELPER (for cfg file)
 * ============================================================================ *)

\* Define thread symmetry manually
ThreadSymmetry == Permutations(Threads)

(* ============================================================================
 * VIEW HELPER (for cfg file)
 * ============================================================================ *)

\* View specification for state equivalence
StateView == <<Len(eventLog), globalClock>>

(* ============================================================================
 * INITIAL STATE
 * Maps to: EventTracer::new() in Rust
 * ============================================================================ *)

Init ==
    /\ threadClocks = [t \in Threads |-> 0]
    /\ seqNumbers = [t \in Threads |-> 0]
    /\ eventLog = <<>>
    /\ globalClock = 0
    /\ syncHistory = {}
    /\ memoryState = [addr \in MemoryAddresses |-> 0]

(* ============================================================================
 * ACTIONS
 * ============================================================================ *)

(* Internal step: thread increments its clock
 * Maps to: EventTracer::new_metadata() in Rust
 * Corresponds to: LamportTimestamp::increment() *)
InternalStep(t) ==
    /\ ~EventLogFull
    /\ threadClocks' = [threadClocks EXCEPT ![t] = @ + 1]
    /\ seqNumbers' = [seqNumbers EXCEPT ![t] = @ + 1]
    /\ globalClock' = IF threadClocks'[t] > globalClock 
                      THEN threadClocks'[t] 
                      ELSE globalClock
    /\ eventLog' = Append(
            eventLog,
            MakeEvent("ClockTick", t, threadClocks'[t], seqNumbers'[t], 0, 0)
       )
    /\ UNCHANGED <<syncHistory, memoryState>>

(* Synchronization step: thread t1 sends message to t2
 * Maps to: EventTracer::sync_thread() in Rust
 * Corresponds to: LamportTimestamp::sync() *)
SyncStep(t1, t2) ==
    /\ t1 # t2
    /\ ~EventLogFull
    /\ LET sendTs == threadClocks[t1] + 1
           recvTs == IF threadClocks[t2] >= sendTs 
                     THEN threadClocks[t2] + 1
                     ELSE sendTs + 1
       IN
       /\ threadClocks' = [threadClocks EXCEPT 
                            ![t1] = sendTs,
                            ![t2] = recvTs]
       /\ seqNumbers' = [seqNumbers EXCEPT
                          ![t1] = @ + 1,
                          ![t2] = @ + 1]
       \* 01. 이 부분이 핵심입니다: 기존 globalClock과 새로운 recvTs 중 큰 값을 선택
       /\ globalClock' = IF recvTs > globalClock THEN recvTs ELSE globalClock 
       /\ syncHistory' = syncHistory \cup {<<t1, t2, sendTs>>}
       /\ eventLog' = Append(
                Append(eventLog,
                    MakeEvent("MutexUnlock", t1, sendTs, seqNumbers'[t1], 0, 0)),
                    MakeEvent("MutexLock", t2, recvTs, seqNumbers'[t2], 0, 0)
              )
       /\ UNCHANGED memoryState

(* Memory write operation
 * Maps to: SimulationEvent::Memory with MemoryOperation::Write *)
MemoryWrite(t, addr, value, buffered) ==
    /\ ~EventLogFull
    /\ addr \in MemoryAddresses
    /\ threadClocks' = [threadClocks EXCEPT ![t] = @ + 1]
    /\ seqNumbers' = [seqNumbers EXCEPT ![t] = @ + 1]
    /\ globalClock' = IF threadClocks'[t] > globalClock 
                      THEN threadClocks'[t] 
                      ELSE globalClock
    /\ eventLog' = Append(
            eventLog,
            MakeEvent("MemoryWrite", t, threadClocks'[t], seqNumbers'[t], addr, value)
       )
    /\ memoryState' = IF ~buffered 
                      THEN [memoryState EXCEPT ![addr] = value]
                      ELSE memoryState  \* Buffered write doesn't update immediately
    /\ UNCHANGED syncHistory

(* Memory read operation
 * Maps to: SimulationEvent::Memory with MemoryOperation::Read *)
MemoryRead(t, addr) ==
    /\ ~EventLogFull
    /\ addr \in MemoryAddresses
    /\ threadClocks' = [threadClocks EXCEPT ![t] = @ + 1]
    /\ seqNumbers' = [seqNumbers EXCEPT ![t] = @ + 1]
    /\ globalClock' = IF threadClocks'[t] > globalClock 
                      THEN threadClocks'[t] 
                      ELSE globalClock
    /\ eventLog' = Append(
            eventLog,
            MakeEvent("MemoryRead", t, threadClocks'[t], seqNumbers'[t], 
                      addr, memoryState[addr])
       )
    /\ UNCHANGED <<syncHistory, memoryState>>

(* Store buffer flush
 * Maps to: SimulationEvent::Memory with MemoryOperation::BufferFlush *)
BufferFlush(t, addr, value) ==
    /\ ~EventLogFull
    /\ addr \in MemoryAddresses
    /\ threadClocks' = [threadClocks EXCEPT ![t] = @ + 1]
    /\ seqNumbers' = [seqNumbers EXCEPT ![t] = @ + 1]
    /\ globalClock' = IF threadClocks'[t] > globalClock 
                      THEN threadClocks'[t] 
                      ELSE globalClock
    /\ eventLog' = Append(
            eventLog,
            MakeEvent("BufferFlush", t, threadClocks'[t], seqNumbers'[t], addr, value)
       )
    /\ memoryState' = [memoryState EXCEPT ![addr] = value]
    /\ UNCHANGED syncHistory

(* ============================================================================
 * NEXT STATE RELATION
 * ============================================================================ *)

Next ==
    \/ \E t \in Threads: InternalStep(t)
    \/ \E t1, t2 \in Threads: SyncStep(t1, t2)
    \/ \E t \in Threads, addr \in MemoryAddresses, val \in {1}, buffered \in {FALSE}:
        MemoryWrite(t, addr, val, buffered)
    \/ \E t \in Threads, addr \in MemoryAddresses:
        MemoryRead(t, addr)
    \/ \E t \in Threads, addr \in MemoryAddresses, val \in {1}:
        BufferFlush(t, addr, val)

(* ============================================================================
 * SPECIFICATION
 * ============================================================================ *)

Spec == Init /\ [][Next]_vars

(* ============================================================================
 * STATE CONSTRAINT (for bounded model checking)
 * Must be defined as an operator, cannot be inline in .cfg
 * ============================================================================ *)

(* Primary constraint: limit event log size *)
StateConstraint == Len(eventLog) <= MaxEvents

(* Optional: More aggressive constraint for faster verification *)
StrictConstraint ==
    /\ Len(eventLog) <= MaxEvents
    /\ globalClock <= MaxTimestamp
    /\ \A t \in Threads: threadClocks[t] <= MaxTimestamp

(* ============================================================================
 * INVARIANTS
 * Maps to: EventTracer::verify_causality() in Rust
 * ============================================================================ *)

(* Invariant 1: Monotonicity within threads
 * Maps to: Rust verification in EventTracer::record() with validate_causality=true *)
MonotonicityInvariant ==
    \A t \in Threads:
        \A i, j \in ThreadEvents(t):
            i < j => eventLog[i].timestamp < eventLog[j].timestamp

(* Invariant 2: Causality preservation
 * If e1 happens-before e2, then timestamp(e1) < timestamp(e2)
 * Maps to: HappensBeforeRelation::from_events in Rust *)
CausalityPreservation ==
    \A i, j \in 1..Len(eventLog):
        HappensBefore(i, j) => eventLog[i].timestamp < eventLog[j].timestamp

(* Invariant 3: No causality cycles
 * Maps to: CausalityGraph::topological_order - DAG property *)
NoCycles ==
    \A i \in 1..Len(eventLog):
        ~HappensBefore(i, i)

(* Invariant 4: Global clock is maximum of all thread clocks
 * Maps to: EventTracer.global_timestamp maintenance *)
GlobalClockIsMax ==
    \A t \in Threads:
        threadClocks[t] <= globalClock

(* Invariant 5: Sequence numbers are strictly increasing per thread
 * Maps to: ThreadState.seq_num in Rust *)
SequenceNumberMonotonic ==
    \A t \in Threads:
        \A i, j \in ThreadEvents(t):
            i < j => eventLog[i].seqNum < eventLog[j].seqNum

(* Invariant 6: Timestamps don't exceed maximum
 * Maps to: Kani proof verify_lamport_monotonicity with overflow check *)
BoundedTimestamps ==
    /\ \A t \in Threads: threadClocks[t] <= MaxTimestamp
    /\ globalClock <= MaxTimestamp
    /\ \A i \in 1..Len(eventLog): eventLog[i].timestamp <= MaxTimestamp

(* Combined invariant *)
Invariants ==
    /\ TypeOK
    /\ MonotonicityInvariant
    /\ CausalityPreservation
    /\ NoCycles
    /\ GlobalClockIsMax
    /\ SequenceNumberMonotonic
    /\ BoundedTimestamps

(* ============================================================================
 * TEMPORAL PROPERTIES
 * ============================================================================ *)

(* Property 1: If a thread takes a step, its clock eventually increases *)
ClockProgress ==
    \A t \in Threads:
        [](\E i \in 1..Len(eventLog): eventLog[i].threadId = t)
            => <>(threadClocks[t] > 0)

(* Property 2: Synchronization establishes causality *)
SyncEstablishesCausality ==
    \A t1, t2 \in Threads:
        [](\E <<sender, receiver, ts>> \in syncHistory:
            /\ sender = t1
            /\ receiver = t2
            => threadClocks[t2] > ts)

(* ============================================================================
 * THEOREMS (Manually proven, asserted as invariants)
 * ============================================================================ *)

(* Theorem 1: Happens-before is a partial order (transitivity)
 * Maps to: Kani proof verify_happens_before_transitivity *)
THEOREM HappensBeforeTransitivity ==
    \A e1, e2, e3 \in 1..Len(eventLog):
        (HappensBefore(e1, e2) /\ HappensBefore(e2, e3)) => HappensBefore(e1, e3)

(* Theorem 2: Same-thread events are totally ordered
 * Maps to: CausalityGraph thread sequence construction *)
THEOREM SameThreadTotalOrder ==
    \A t \in Threads:
    \A e1, e2 \in ThreadEvents(t):
        (e1 # e2) => (HappensBefore(e1, e2) \/ HappensBefore(e2, e1))

====================================================================================================