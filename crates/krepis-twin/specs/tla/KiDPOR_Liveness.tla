------------------------- MODULE KiDPOR_Liveness -------------------------
(****************************************************************************)
(* Ki-DPOR with Liveness & Fairness Checking                               *)
(* Phase: 1D (Week 7-8)                                                     *)
(****************************************************************************)

EXTENDS KiDPOR, Naturals

-----------------------------------------------------------------------------
(* CONSTANTS FOR LIVENESS                                                  *)
-----------------------------------------------------------------------------

CONSTANTS
    MaxStarvationLimit,     \* Maximum steps a thread can be starved
    MaxLivelockCycles       \* Maximum repeated state visits before livelock

ASSUME
    /\ MaxStarvationLimit \in Nat
    /\ MaxStarvationLimit > 0
    /\ MaxLivelockCycles \in Nat
    /\ MaxLivelockCycles > 0

-----------------------------------------------------------------------------
(* LIVENESS VARIABLES                                                      *)
-----------------------------------------------------------------------------

VARIABLES
    starvation_counters,    \* [Threads -> Nat] Steps since last progress
    liveness_history,       \* Seq(StateSignature) For livelock detection
    fairness_stats          \* Statistics for fairness analysis

liveness_vars == <<starvation_counters, liveness_history, fairness_stats>>
all_liveness_vars == <<all_vars, liveness_vars>>

-----------------------------------------------------------------------------
(* HELPER FUNCTIONS                                                        *)
-----------------------------------------------------------------------------

RECURSIVE SumSeq(_)
SumSeq(seq) ==
    IF seq = <<>> THEN 0
    ELSE Head(seq) + SumSeq(Tail(seq))

-----------------------------------------------------------------------------
(* EXTENDED EXECUTION STATE TYPE DEFINITION                                *)
-----------------------------------------------------------------------------

(****************************************************************************)
(* LivenessExecutionStateSet: 상태들의 "집합(Type)" 정의                    *)
(* [key: Set] 문법을 사용하여 레코드의 타입을 정의합니다.                   *)
(****************************************************************************)
LivenessExecutionStateSet == [
    path: Seq(StepRecord),
    cost_g: Nat,
    heuristic_h: Nat,
    priority_f: Nat,
    resource_state: [Resources -> ResourceState],
    waiting_queues_state: [Resources -> Seq(Threads)],
    thread_status_state: [Threads -> ThreadStatusValues],
    clock_state: [Threads -> [Threads -> Nat]],
    blocked_on_state: [Threads -> Resources \cup {Null}],
    wfg_state: [Threads -> SUBSET Threads],
    
    \* Liveness fields
    starvation_counters_state: [Threads -> Nat],
    last_progress: [Threads -> Nat],
    fairness_score: Nat
]

-----------------------------------------------------------------------------
(* STARVATION DETECTION                                                    *)
-----------------------------------------------------------------------------

UpdateStarvationCounters(state, executed_thread) ==
    [t \in Threads |->
        IF t = executed_thread
        THEN 0  \* Reset
        ELSE IF state.thread_status_state[t] \in {"Running", "Blocked"}
             THEN state.starvation_counters_state[t] + 1  \* Increment
             ELSE state.starvation_counters_state[t]      \* No change
    ]

IsStarving(state, thread) ==
    state.starvation_counters_state[thread] > MaxStarvationLimit

TotalStarvation(state) ==
    LET counters == {state.starvation_counters_state[t] : t \in Threads}
    IN SumSeq(SetToSeq(counters))

MaxStarvation(state) ==
    LET counters == {state.starvation_counters_state[t] : t \in Threads}
    IN CHOOSE max \in counters :
        \A c \in counters : c <= max

-----------------------------------------------------------------------------
(* LIVELOCK DETECTION                                                      *)
-----------------------------------------------------------------------------

StateSignatureRepeats(history, sig) ==
    Len([i \in DOMAIN history |-> IF history[i] = sig THEN 1 ELSE 0])

IsLivelocked(history, current_sig) ==
    StateSignatureRepeats(history, current_sig) >= MaxLivelockCycles

-----------------------------------------------------------------------------
(* FAIRNESS-AWARE HEURISTIC                                                *)
-----------------------------------------------------------------------------

LivenessHeuristic(state) ==
    LET \* Original danger metrics
        blocked == BlockedThreadCount(state)
        contention == ContentionScore(state)
        interleaving == InterleaveComplexity(state)
        danger_score == (blocked * 100) + (contention * 10) + (interleaving * 5)
        
        \* Fairness metrics
        total_starvation == TotalStarvation(state)
        max_starvation == MaxStarvation(state)
        fairness_score == (total_starvation * 50) + (max_starvation * 20)
        
        \* Combined score
        combined_danger == danger_score + fairness_score
        max_danger == 2000 
    IN max_danger - combined_danger

ComputeFairnessScore(state) ==
    LET max_counter == MaxStarvation(state)
        avg_counter == TotalStarvation(state) \div Cardinality(Threads)
    IN (max_counter * 2) + avg_counter

-----------------------------------------------------------------------------
(* INITIAL STATE WITH LIVENESS (OVERRIDE)                                  *)
-----------------------------------------------------------------------------

LivenessInit ==
    /\ Init  \* ResourceOracle Init
    /\ starvation_counters = [t \in Threads |-> 0]
    /\ liveness_history = <<>>
    /\ fairness_stats = [max_starvation |-> 0, total_steps |-> 0, unfair_states |-> 0]
    
    /\ LET initial_counters == [t \in Threads |-> 0]
           initial_state == [
               path |-> <<>>,
               cost_g |-> 0,
               heuristic_h |-> 0, 
               priority_f |-> 0,
               resource_state |-> resources,
               waiting_queues_state |-> waiting_queues,
               thread_status_state |-> thread_status,
               blocked_on_state |-> blocked_on,
               wfg_state |-> wait_for_graph,
               clock_state |-> [t1 \in Threads |-> [t2 \in Threads |-> 0]],
               starvation_counters_state |-> initial_counters,
               last_progress |-> [t \in Threads |-> 0],
               fairness_score |-> 0
           ]
           
           h == LivenessHeuristic(initial_state)
           final_initial_state == [initial_state EXCEPT 
               !.heuristic_h = h,
               !.priority_f = h 
           ]
       IN 
           /\ priority_queue = <<final_initial_state>>
           /\ explored_set = {}
           /\ current_state = final_initial_state
           /\ stats = [explored |-> 0, queue_max |-> 1, expansions |-> 0]

-----------------------------------------------------------------------------
(* STATE EXPANSION WITH LIVENESS TRACKING                                 *)
-----------------------------------------------------------------------------

ExpandStateWithLiveness ==
    /\ ~PQEmpty
    /\ LET popped == PQPop(priority_queue)
           curr == popped.state
           remaining_pq == popped.remaining
           curr_sig == StateSignature(curr)
       IN
           /\ current_state' = curr
           /\ explored_set' = explored_set \cup {curr_sig}
           
           \* Check for livelock
           /\ ~IsLivelocked(liveness_history, curr_sig)
           
           \* Update liveness history
           /\ liveness_history' = Append(liveness_history, curr_sig)
           
           \* Generate successors with liveness tracking
           /\ LET enabled == EnabledThreads(curr)
              IN \A t \in enabled :
                  \E op \in Operations, r \in Resources :
                      LET new_step == [thread |-> t, op |-> op, 
                                       resource |-> r, depth |-> Len(curr.path)]
                          new_path == Append(curr.path, new_step)
                          new_g == curr.cost_g + 1
                          
                          \* Update starvation counters
                          new_counters == UpdateStarvationCounters(curr, t)
                          
                          \* Check if any thread is starving
                          has_starvation == \E thread \in Threads :
                              new_counters[thread] > MaxStarvationLimit
                          
                          \* Build new state (Using NextSnapshot from KiDPOR)
                          next_snap == NextSnapshot(curr, t, op, r)
                          
                          new_state == [
                              path |-> new_path,
                              cost_g |-> new_g,
                              heuristic_h |-> 0,
                              priority_f |-> 0,
                              resource_state |-> next_snap.res,
                              waiting_queues_state |-> next_snap.q,
                              thread_status_state |-> next_snap.sts,
                              blocked_on_state |-> next_snap.blk,
                              wfg_state |-> next_snap.wfg,
                              clock_state |-> curr.clock_state,
                              starvation_counters_state |-> new_counters,
                              last_progress |-> [curr.last_progress EXCEPT ![t] = new_g],
                              fairness_score |-> ComputeFairnessScore([
                                  starvation_counters_state |-> new_counters
                              ])
                          ]
                          
                          \* Compute liveness-aware heuristic
                          new_h == LivenessHeuristic(new_state)
                          new_f == ComputePriority(new_g, new_h)
                          
                          final_state == [new_state EXCEPT 
                              !.heuristic_h = new_h,
                              !.priority_f = new_f]
                      IN
                          \* Only add if not already explored
                          /\ ~AlreadyExplored(final_state)
                          \* Record if we found starvation
                          /\ IF has_starvation
                             THEN fairness_stats' = [fairness_stats EXCEPT
                                      !.unfair_states = @ + 1]
                             ELSE fairness_stats' = fairness_stats
                          /\ priority_queue' = PQInsert(remaining_pq, final_state)
                          /\ stats' = [stats EXCEPT 
                                  !.explored = @ + 1,
                                  !.queue_max = IF Len(priority_queue') > @
                                               THEN Len(priority_queue')
                                               ELSE @]
           
           (* Update global vars for trace *)
           /\ resources' = curr.resource_state
           /\ waiting_queues' = curr.waiting_queues_state
           /\ thread_status' = curr.thread_status_state
           /\ blocked_on' = curr.blocked_on_state
           /\ wait_for_graph' = curr.wfg_state
           /\ UNCHANGED <<current_time, execution_history, visited_pcs>>

-----------------------------------------------------------------------------
(* LIVENESS PROPERTIES                                                     *)
-----------------------------------------------------------------------------

NoStarvation ==
    /\ \A t \in Threads : starvation_counters[t] <= MaxStarvationLimit
    /\ current_state # Null =>
           \A t \in Threads :
               current_state.starvation_counters_state[t] <= MaxStarvationLimit

NoLivelock ==
    \A sig \in explored_set :
        StateSignatureRepeats(liveness_history, sig) < MaxLivelockCycles

EventualProgress ==
    current_state # Null =>
        \A t \in Threads :
            \/ current_state.starvation_counters_state[t] < MaxStarvationLimit
            \/ \E i \in DOMAIN current_state.path :
                   current_state.path[i].thread = t

ThreadExecutes(t) ==
    /\ current_state # Null
    /\ \E i \in DOMAIN current_state.path :
           /\ current_state.path[i].thread = t
           /\ i = Len(current_state.path)

WeakFairness ==
    \A t \in Threads :
        current_state # Null =>
            (current_state.thread_status_state[t] = "Running") ~>
                ThreadExecutes(t)

-----------------------------------------------------------------------------
(* INVARIANTS                                                              *)
-----------------------------------------------------------------------------

(****************************************************************************)
(* [FIX] LivenessTypeOK: KiTypeOK를 제거하고 직접 타입 정의                 *)
(****************************************************************************)
LivenessTypeOK ==
    /\ priority_queue \in Seq(LivenessExecutionStateSet)
    /\ current_state \in LivenessExecutionStateSet
    
    \* Replicate KiTypeOK checks for other vars
    /\ explored_set \in SUBSET [
           resources: [Resources -> ResourceState], 
           statuses: [Threads -> ThreadStatusValues], 
           queues: [Resources -> Seq(Threads)]
       ]
    /\ TypeOK  \* ResourceOracle TypeOK
    
    \* Liveness vars types
    /\ starvation_counters \in [Threads -> Nat]
    /\ liveness_history \in Seq([
           resources: [Resources -> ResourceState],
           statuses: [Threads -> ThreadStatusValues],
           queues: [Resources -> Seq(Threads)]
       ])
    /\ fairness_stats \in [
           max_starvation: Nat,
           total_steps: Nat,
           unfair_states: Nat
       ]

StarvationCountersBounded ==
    \A t \in Threads : starvation_counters[t] <= MaxStarvationLimit + 1

SafetyAndLiveness ==
    /\ SafetyPreserved 
    /\ NoStarvation
    /\ NoLivelock

-----------------------------------------------------------------------------
(* ACTIONS & SPECIFICATION                                                 *)
-----------------------------------------------------------------------------

LivenessNext ==
    \/ ExpandStateWithLiveness
    \/ (PQEmpty /\ UNCHANGED <<all_liveness_vars>>)

LivenessSpec == LivenessInit /\ [][LivenessNext]_all_liveness_vars

LivenessFairness ==
    /\ WF_all_liveness_vars(ExpandStateWithLiveness)
    /\ \A t \in Threads : WF_all_liveness_vars(ThreadExecutes(t))

FairLivenessSpec == LivenessSpec /\ LivenessFairness

-----------------------------------------------------------------------------
(* TEMPORAL PROPERTIES                                                     *)
-----------------------------------------------------------------------------

StarvationEventuallyDetected ==
    (\E t \in Threads : IsStarving(current_state, t)) ~>
        (fairness_stats.unfair_states > 0)

LivelockEventuallyDetected ==
    (\E sig \in explored_set : 
        StateSignatureRepeats(liveness_history, sig) >= MaxLivelockCycles) ~>
            (~NoLivelock)

BoundedLiveness ==
    []<>(fairness_stats.total_steps <= MaxStarvationLimit =>
            \A t \in Threads : ThreadExecutes(t))

===============================================================================