--------------------------- MODULE VirtualClock ---------------------------
EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANTS MaxTimeNs, MaxEvents, LamportMod

VARIABLES virtualTimeNs, lamportClock, eventQueue

vars == <<virtualTimeNs, lamportClock, eventQueue>>

CreateEvent(t, l) == [time |-> t, lamport |-> l]

Init == 
    /\ virtualTimeNs = 0
    /\ lamportClock = 0
    /\ eventQueue = {}

ScheduleEvent(delay) ==
    /\ virtualTimeNs + delay <= MaxTimeNs
    /\ Cardinality(eventQueue) < MaxEvents
    \* LamportMod를 이용한 순환 구조 적용 (상태 공간을 유한하게 만듦)
    /\ LET newLamport == (lamportClock + 1) % LamportMod
       IN  /\ eventQueue' = eventQueue \cup {CreateEvent(virtualTimeNs + delay, newLamport)}
           /\ lamportClock' = newLamport
           /\ UNCHANGED <<virtualTimeNs>>

Tick ==
    /\ eventQueue /= {}
    /\ LET nextEvent == CHOOSE e \in eventQueue : 
                        \A other \in eventQueue : 
                            \/ e.time < other.time
                            \/ (e.time = other.time /\ e.lamport <= other.lamport)
       IN  /\ virtualTimeNs' = nextEvent.time
           /\ eventQueue' = eventQueue \ {nextEvent}
           \* 큐가 비면 완전히 리셋하여 초기 상태와 병합 유도
           /\ lamportClock' = IF eventQueue' = {} THEN 0 ELSE lamportClock

Next == 
    \/ \E d \in {0, 1, 2, 5}: ScheduleEvent(d)
    \/ Tick

Spec == Init /\ [][Next]_vars

\* Invariants
TypeInvariant == virtualTimeNs \in Nat /\ lamportClock < LamportMod
Safety_TimeBound == virtualTimeNs <= MaxTimeNs
Safety_NoPastEvents == \A e \in eventQueue : e.time >= virtualTimeNs

=============================================================================