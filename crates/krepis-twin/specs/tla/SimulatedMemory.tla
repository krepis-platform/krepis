--------------------------- MODULE SimulatedMemory ---------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS 
    MaxTimeNs,
    MaxEvents,
    NumCores,
    Addresses,
    Values,
    LamportMod      \* Modular lamport to close state space

VARIABLES 
    virtualTimeNs,
    lamportClock,
    eventQueue,
    mainMemory,
    storeBuffers

vars == <<virtualTimeNs, lamportClock, eventQueue, mainMemory, storeBuffers>>

Cores == 1..NumCores
EventTypes == {"WRITE_SYNC", "FENCE"}

\* ==========================================================================
\* TYPED EVENT CONSTRUCTORS
\* ==========================================================================

CreateTypedEvent(type, t, l, core) == 
    [type |-> type, time |-> t, lamport |-> l, core |-> core]

IsMemoryEvent(e) == e.type \in {"WRITE_SYNC", "FENCE"}

\* ==========================================================================
\* DETERMINISTIC EVENT SELECTION (from VirtualClock pattern)
\* ==========================================================================

SelectNextEvent ==
    CHOOSE e \in eventQueue :
        \A other \in eventQueue :
            \/ e.time < other.time
            \/ (e.time = other.time /\ e.lamport <= other.lamport)

\* ==========================================================================
\* STORE BUFFER OPERATIONS
\* ==========================================================================

BufferLookup(core, addr) ==
    LET buf == storeBuffers[core]
        matching == {i \in 1..Len(buf) : buf[i].addr = addr}
    IN  IF matching = {} THEN "NONE"
        ELSE buf[CHOOSE x \in matching : \A y \in matching : x >= y].val

ReadValue(core, addr) ==
    LET bufVal == BufferLookup(core, addr)
    IN  IF bufVal /= "NONE" THEN bufVal ELSE mainMemory[addr]

FlushOneEntry(core) ==
    LET buf == storeBuffers[core]
        entry == Head(buf)
    IN  /\ mainMemory' = [mainMemory EXCEPT ![entry.addr] = entry.val]
        /\ storeBuffers' = [storeBuffers EXCEPT ![core] = Tail(buf)]

\* ==========================================================================
\* INIT
\* ==========================================================================

Init ==
    /\ virtualTimeNs = 0
    /\ lamportClock = 0
    /\ eventQueue = {}
    /\ mainMemory = [a \in Addresses |-> 0]
    /\ storeBuffers = [c \in Cores |-> <<>>]

\* ==========================================================================
\* ACTIONS
\* ==========================================================================

\* Write: Buffer locally + schedule sync event (atomic)
Write(core, addr, val) ==
    /\ virtualTimeNs + 1 <= MaxTimeNs
    /\ Cardinality(eventQueue) < MaxEvents
    /\ Len(storeBuffers[core]) < 2              \* STRICT: max 2 pending per core
    /\ LET newLamport == (lamportClock + 1) % LamportMod
           syncTime == virtualTimeNs + 1        \* Propagate on NEXT tick (deterministic)
       IN  /\ storeBuffers' = [storeBuffers EXCEPT 
                ![core] = Append(@, [addr |-> addr, val |-> val])]
           /\ eventQueue' = eventQueue \cup 
                {CreateTypedEvent("WRITE_SYNC", syncTime, newLamport, core)}
           /\ lamportClock' = newLamport
    /\ UNCHANGED <<virtualTimeNs, mainMemory>>

\* Tick: Advance time AND process memory events atomically
Tick ==
    /\ eventQueue /= {}
    /\ LET nextEvent == SelectNextEvent
       IN  /\ virtualTimeNs' = nextEvent.time
           /\ eventQueue' = eventQueue \ {nextEvent}
           \* DETERMINISTIC: If memory event, propagate immediately
           /\ IF IsMemoryEvent(nextEvent) /\ storeBuffers[nextEvent.core] /= <<>>
              THEN FlushOneEntry(nextEvent.core)
              ELSE UNCHANGED <<mainMemory, storeBuffers>>
           \* Reset lamport when queue empties
           /\ lamportClock' = IF eventQueue' = {} THEN 0 ELSE lamportClock

\* Fence: Flush all + schedule confirmation (for litmus tests)
Fence(core) ==
    /\ storeBuffers[core] /= <<>>
    /\ Cardinality(eventQueue) < MaxEvents
    /\ LET buf == storeBuffers[core]
           newMem == [a \in Addresses |->
               LET writes == {i \in 1..Len(buf) : buf[i].addr = a}
               IN  IF writes = {} THEN mainMemory[a]
                   ELSE buf[CHOOSE x \in writes : \A y \in writes : x >= y].val]
       IN  /\ mainMemory' = newMem
           /\ storeBuffers' = [storeBuffers EXCEPT ![core] = <<>>]
    /\ UNCHANGED <<virtualTimeNs, lamportClock, eventQueue>>

\* ==========================================================================
\* SPECIFICATION
\* ==========================================================================

Next ==
    \/ Tick
    \/ \E c \in Cores, a \in Addresses, v \in Values \ {0}: Write(c, a, v)
    \/ \E c \in Cores: Fence(c)

Spec == Init /\ [][Next]_vars /\ WF_vars(Tick)

\* ==========================================================================
\* INVARIANTS
\* ==========================================================================

TypeInvariant ==
    /\ virtualTimeNs \in 0..MaxTimeNs
    /\ lamportClock \in 0..(LamportMod - 1)
    /\ mainMemory \in [Addresses -> Values]
    /\ \A c \in Cores: Len(storeBuffers[c]) <= 2

Safety_TimeBound == virtualTimeNs <= MaxTimeNs
Safety_BoundedQueue == Cardinality(eventQueue) <= MaxEvents
Safety_BoundedBuffers == \A c \in Cores: Len(storeBuffers[c]) <= 2

\* ==========================================================================
\* LITMUS: Store Buffering Detection
\* ==========================================================================

\* SC violation possible when both cores have pending writes to different addrs
SCViolationState ==
    /\ NumCores >= 2
    /\ Cardinality(Addresses) >= 2
    /\ \E a1, a2 \in Addresses : a1 /= a2 /\
       \E i \in 1..Len(storeBuffers[1]) : storeBuffers[1][i].addr = a1 /\
       \E j \in 1..Len(storeBuffers[2]) : storeBuffers[2][j].addr = a2 /\
       mainMemory[a1] = 0 /\ mainMemory[a2] = 0

NoSCViolation == ~SCViolationState

=============================================================================