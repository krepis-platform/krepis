---------------------------- MODULE SchedulerOracle ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS MaxTimeNs, MaxEvents, Threads, LamportMod, Strategy

ASSUME Strategy \in {"PRODUCTION", "VERIFICATION"}

VARIABLES virtualTimeNs, lamportClock, eventQueue, threadStates

vars == <<virtualTimeNs, lamportClock, eventQueue, threadStates>>

ThreadStates == {"RUNNABLE", "BLOCKED", "COMPLETED"}

CreateEvent(t, l, eid, thread) ==
    [time |-> t, lamport |-> l, eventId |-> eid, thread |-> thread]

\* [FIX] Removed 'e.time <= virtualTimeNs'. 
\* In Virtual Time, we look ahead to the earliest future event.
RunnableEvents ==
    {e \in eventQueue :
        threadStates[e.thread] = "RUNNABLE"
    }

Init ==
    /\ virtualTimeNs = 0
    /\ lamportClock = 0
    /\ eventQueue = {}
    /\ threadStates = [t \in Threads |-> "RUNNABLE"]

ScheduleEvent(thread, delay) ==
    /\ virtualTimeNs + delay <= MaxTimeNs
    /\ Cardinality(eventQueue) < MaxEvents
    /\ thread \in Threads
    /\ LET newLamport == (lamportClock + 1) % LamportMod
           newEventId == Cardinality(eventQueue) + 1
           newEvent == CreateEvent(virtualTimeNs + delay, newLamport, 
                                   newEventId, thread)
       IN  /\ eventQueue' = eventQueue \cup {newEvent}
           /\ lamportClock' = newLamport
           /\ threadStates' = [threadStates EXCEPT ![thread] = "RUNNABLE"]
           /\ UNCHANGED virtualTimeNs

ExecuteNext_Production ==
    /\ Strategy = "PRODUCTION"
    /\ RunnableEvents /= {}
    \* CHOOSE logic acts as the "Time Jump" mechanism
    /\ LET nextEvent == CHOOSE e \in RunnableEvents :
                            \A other \in RunnableEvents :
                                \/ e.time < other.time
                                \/ (e.time = other.time /\ e.lamport < other.lamport)
                                \/ (e.time = other.time /\ e.lamport = other.lamport 
                                    /\ e.eventId <= other.eventId)
       IN  /\ virtualTimeNs' = nextEvent.time  \* Time Jumps Here!
           /\ eventQueue' = eventQueue \ {nextEvent}
           /\ UNCHANGED <<lamportClock, threadStates>>

ExecuteNext_Verification ==
    /\ Strategy = "VERIFICATION"
    /\ RunnableEvents /= {}
    /\ \E nextEvent \in RunnableEvents :
           /\ virtualTimeNs' = nextEvent.time
           /\ eventQueue' = eventQueue \ {nextEvent}
           /\ UNCHANGED <<lamportClock, threadStates>>

Next ==
    \/ \E t \in Threads, d \in {1, 5} : ScheduleEvent(t, d)
    \/ ExecuteNext_Production
    \/ ExecuteNext_Verification

Spec == Init /\ [][Next]_vars

TypeInvariant ==
    /\ virtualTimeNs \in 0..MaxTimeNs
    /\ lamportClock \in 0..(LamportMod-1)
    /\ eventQueue \subseteq [
           time: 0..MaxTimeNs, 
           lamport: 0..(LamportMod-1), 
           eventId: Nat,
           thread: Threads
       ]
    /\ threadStates \in [Threads -> ThreadStates]

Safety_TimeBound == virtualTimeNs <= MaxTimeNs

Safety_BoundedQueue == Cardinality(eventQueue) <= MaxEvents

=============================================================================