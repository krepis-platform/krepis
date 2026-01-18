---------------------------- MODULE ResourceOracle ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Threads,
    Resources,
    Mutexes,
    Semaphores,
    MaxProgramCounter,
    MaxHistoryLen,
    Null

ASSUME
    /\ Threads # {}
    /\ Resources # {}
    /\ Mutexes \subseteq Resources
    /\ Semaphores \subseteq Resources
    /\ Mutexes \cap Semaphores = {}
    /\ Mutexes \cup Semaphores = Resources
    /\ MaxProgramCounter \in Nat
    /\ MaxHistoryLen \in Nat
    /\ Null \notin Threads
    /\ Null \notin Resources

IsMutex(r) == r \in Mutexes
IsSemaphore(r) == r \in Semaphores

-----------------------------------------------------------------------------

VARIABLES
    resources,
    waiting_queues,
    thread_status,
    blocked_on,
    wait_for_graph,
    execution_history,
    visited_pcs,
    current_time

vars == <<resources, waiting_queues, thread_status, blocked_on, 
          wait_for_graph, execution_history, visited_pcs, current_time>>

-----------------------------------------------------------------------------

ThreadStatusValues == {"Running", "Blocked", "Finished"}

ResourceState == [
    owner: Threads \cup {Null},
    count: Nat
]

HistoryEntry == [
    thread: Threads,
    pc: Nat,
    timestamp: Nat
]

TypeOK ==
    /\ resources \in [Resources -> ResourceState]
    /\ waiting_queues \in [Resources -> Seq(Threads)]
    /\ thread_status \in [Threads -> ThreadStatusValues]
    /\ blocked_on \in [Threads -> Resources \cup {Null}]
    /\ wait_for_graph \in [Threads -> SUBSET Threads]
    /\ execution_history \in Seq(HistoryEntry)
    /\ Len(execution_history) <= MaxHistoryLen
    /\ visited_pcs \in [Threads -> SUBSET Nat]
    /\ current_time \in Nat

-----------------------------------------------------------------------------

Init ==
    /\ resources = [r \in Resources |-> 
        [owner |-> Null,
         count |-> IF IsSemaphore(r) THEN 1 ELSE 0]]
    /\ waiting_queues = [r \in Resources |-> <<>>]
    /\ thread_status = [t \in Threads |-> "Running"]
    /\ blocked_on = [t \in Threads |-> Null]
    /\ wait_for_graph = [t \in Threads |-> {}]
    /\ execution_history = <<>>
    /\ visited_pcs = [t \in Threads |-> {}]
    /\ current_time = 0

-----------------------------------------------------------------------------

RequestResource(t, r) ==
    /\ thread_status[t] = "Running"
    /\ blocked_on[t] = Null
    /\ resources[r].owner /= t
    /\ IF IsMutex(r) THEN
           IF resources[r].owner = Null THEN
               /\ resources' = [resources EXCEPT ![r].owner = t]
               /\ thread_status' = thread_status
               /\ blocked_on' = blocked_on
               /\ waiting_queues' = waiting_queues
               /\ wait_for_graph' = wait_for_graph
           ELSE
               /\ waiting_queues' = [waiting_queues EXCEPT ![r] = Append(@, t)]
               /\ thread_status' = [thread_status EXCEPT ![t] = "Blocked"]
               /\ blocked_on' = [blocked_on EXCEPT ![t] = r]
               /\ resources' = resources
               /\ wait_for_graph' = [wait_for_graph EXCEPT 
                   ![t] = @ \cup {resources[r].owner}]
       ELSE
           IF resources[r].count > 0 THEN
               /\ resources' = [resources EXCEPT 
                   ![r].count = @ - 1,
                   ![r].owner = t]
               /\ thread_status' = thread_status
               /\ blocked_on' = blocked_on
               /\ waiting_queues' = waiting_queues
               /\ wait_for_graph' = wait_for_graph
           ELSE
               /\ waiting_queues' = [waiting_queues EXCEPT ![r] = Append(@, t)]
               /\ thread_status' = [thread_status EXCEPT ![t] = "Blocked"]
               /\ blocked_on' = [blocked_on EXCEPT ![t] = r]
               /\ resources' = resources
               /\ wait_for_graph' = [wait_for_graph EXCEPT 
                   ![t] = @ \cup {resources[r].owner}]
    /\ UNCHANGED <<execution_history, visited_pcs, current_time>>

ReleaseResource(t, r) ==
    /\ thread_status[t] = "Running"
    /\ resources[r].owner = t
    /\ LET waiters == waiting_queues[r]
       IN IF Len(waiters) > 0 THEN
              LET next_thread == Head(waiters)
                  remaining == Tail(waiters)
              IN IF IsMutex(r) THEN
                     /\ resources' = [resources EXCEPT ![r].owner = next_thread]
                     /\ waiting_queues' = [waiting_queues EXCEPT ![r] = remaining]
                     /\ thread_status' = [thread_status EXCEPT ![next_thread] = "Running"]
                     /\ blocked_on' = [blocked_on EXCEPT ![next_thread] = Null]
                     /\ wait_for_graph' = [wait_for_graph EXCEPT ![next_thread] = @ \ {t}]
                 ELSE
                     /\ resources' = [resources EXCEPT 
                         ![r].owner = next_thread,
                         ![r].count = @]
                     /\ waiting_queues' = [waiting_queues EXCEPT ![r] = remaining]
                     /\ thread_status' = [thread_status EXCEPT ![next_thread] = "Running"]
                     /\ blocked_on' = [blocked_on EXCEPT ![next_thread] = Null]
                     /\ wait_for_graph' = [wait_for_graph EXCEPT ![next_thread] = @ \ {t}]
          ELSE
              IF IsMutex(r) THEN
                  /\ resources' = [resources EXCEPT ![r].owner = Null]
                  /\ UNCHANGED <<waiting_queues, thread_status, blocked_on, wait_for_graph>>
              ELSE
                  /\ resources' = [resources EXCEPT 
                      ![r].count = @ + 1,
                      ![r].owner = Null]
                  /\ UNCHANGED <<waiting_queues, thread_status, blocked_on, wait_for_graph>>
    /\ UNCHANGED <<execution_history, visited_pcs, current_time>>

Step(t, pc) ==
    /\ thread_status[t] = "Running"
    /\ pc <= MaxProgramCounter
    /\ LET new_entry == [thread |-> t, pc |-> pc, timestamp |-> current_time]
           trimmed == IF Len(execution_history) >= MaxHistoryLen
                      THEN Tail(execution_history)
                      ELSE execution_history
       IN /\ execution_history' = Append(trimmed, new_entry)
          /\ visited_pcs' = [visited_pcs EXCEPT ![t] = @ \cup {pc}]
          /\ current_time' = current_time + 1
    /\ UNCHANGED <<resources, waiting_queues, thread_status, blocked_on, wait_for_graph>>

Finish(t) ==
    /\ thread_status[t] = "Running"
    /\ \A r \in Resources : resources[r].owner /= t
    /\ thread_status' = [thread_status EXCEPT ![t] = "Finished"]
    /\ UNCHANGED <<resources, waiting_queues, blocked_on, wait_for_graph, 
                   execution_history, visited_pcs, current_time>>

-----------------------------------------------------------------------------

RECURSIVE TransitiveClosure(_)
TransitiveClosure(graph) ==
    LET one_step == [t \in DOMAIN graph |-> 
                        graph[t] \cup UNION {graph[s] : s \in graph[t] \cap DOMAIN graph}]
    IN IF one_step = graph THEN graph ELSE TransitiveClosure(one_step)

HasCycle ==
    LET closure == TransitiveClosure(wait_for_graph)
    IN \E t \in Threads : t \in closure[t]

DeadlockedThreads ==
    {t \in Threads : t \in TransitiveClosure(wait_for_graph)[t]}
        
TimeConstraint == current_time <= 20

-----------------------------------------------------------------------------

NoDeadlock == ~HasCycle

MutualExclusion ==
    \A r \in Mutexes :
        resources[r].owner # Null =>
            \A t \in Threads \ {resources[r].owner} :
                resources[r].owner # t

NoOrphanedWaiters ==
    \A t \in Threads :
        thread_status[t] = "Blocked" =>
            /\ blocked_on[t] # Null
            /\ \E i \in DOMAIN waiting_queues[blocked_on[t]] :
                waiting_queues[blocked_on[t]][i] = t

-----------------------------------------------------------------------------

Terminating ==
    /\ \A t \in Threads : thread_status[t] = "Finished"
    /\ UNCHANGED vars

Next ==
    \/ \E t \in Threads, r \in Resources : RequestResource(t, r)
    \/ \E t \in Threads, r \in Resources : ReleaseResource(t, r)
    \/ \E t \in Threads, pc \in 0..MaxProgramCounter : Step(t, pc)
    \/ \E t \in Threads : Finish(t)
    \/ Terminating

Spec == Init /\ [][Next]_vars

Liveness ==
    <>(\A t \in Threads : thread_status[t] \in {"Finished", "Blocked"})

===============================================================================