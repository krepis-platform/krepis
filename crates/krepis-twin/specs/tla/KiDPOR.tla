---------------------------- MODULE KiDPOR ------------------------------------
(****************************************************************************)
(* Ki-DPOR - Krepis Intelligent Dynamic Partial Order Reduction            *)
(* Phase: 1C (Week 5-6)                                                     *)
(****************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, TLC, ResourceOracle

-----------------------------------------------------------------------------
(* CONSTANTS                                                                *)
-----------------------------------------------------------------------------

CONSTANTS
    MaxDepth,           
    Operations,         
    HeuristicWeight     

ASSUME
    /\ MaxDepth \in Nat
    /\ MaxDepth > 0
    /\ Operations # {}
    /\ HeuristicWeight \in Nat

-----------------------------------------------------------------------------
(* EXECUTION STATE                                                          *)
-----------------------------------------------------------------------------

StepRecord == [
    thread: Threads,
    op: Operations,
    resource: Resources,
    depth: Nat
]

(****************************************************************************)
(* [FIX] ExecutionState: blocked_on과 wfg 상태 추가 (데드락 감지용)         *)
(****************************************************************************)
ExecutionState == [
    path: Seq(StepRecord),
    cost_g: Nat,
    heuristic_h: Nat,
    priority_f: Nat,
    (* ResourceOracle State Replicas *)
    resource_state: [Resources -> ResourceState],
    waiting_queues_state: [Resources -> Seq(Threads)],
    thread_status_state: [Threads -> ThreadStatusValues],
    blocked_on_state: [Threads -> Resources \cup {Null}],
    wfg_state: [Threads -> SUBSET Threads],
    clock_state: [Threads -> [Threads -> Nat]]
]

-----------------------------------------------------------------------------
(* HELPER FUNCTIONS                                                         *)
-----------------------------------------------------------------------------

RECURSIVE SumQueues(_, _)
SumQueues(rs, q_state) ==
    IF rs = {} THEN 0
    ELSE LET r == CHOOSE x \in rs : TRUE
         IN Len(q_state[r]) + SumQueues(rs \ {r}, q_state)

RECURSIVE SetToSeq(_)
SetToSeq(S) ==
    IF S = {} THEN <<>>
    ELSE LET x == CHOOSE x \in S : TRUE
         IN <<x>> \o SetToSeq(S \ {x})

-----------------------------------------------------------------------------
(* HEURISTIC FUNCTION                                                       *)
-----------------------------------------------------------------------------

BlockedThreadCount(state) ==
    Cardinality({t \in Threads : state.thread_status_state[t] = "Blocked"})

ContentionScore(state) ==
    SumQueues(Resources, state.waiting_queues_state)

InterleaveComplexity(state) ==
    Cardinality({state.path[i].thread : i \in DOMAIN state.path})

Heuristic(state) ==
    LET blocked == BlockedThreadCount(state)
        contention == ContentionScore(state)
        interleaving == InterleaveComplexity(state)
        danger_score == (blocked * 100) + (contention * 10) + (interleaving * 5)
        max_danger == 1000 
    IN max_danger - danger_score

ComputePriority(g, h) ==
    g + (HeuristicWeight * h)

-----------------------------------------------------------------------------
(* PRIORITY QUEUE                                                           *)
-----------------------------------------------------------------------------

VARIABLES
    priority_queue,     
    explored_set,       
    current_state,      
    stats               

ki_vars == <<priority_queue, explored_set, current_state, stats>>
all_vars == <<ki_vars, vars>> 

PQEmpty ==
    Len(priority_queue) = 0

PQInsert(pq, state) ==
    LET insert_pos == 
        CHOOSE i \in 1..Len(pq)+1 :
            /\ \A j \in 1..i-1 : pq[j].priority_f <= state.priority_f
            /\ \A j \in i..Len(pq) : state.priority_f <= pq[j].priority_f
        new_pq == SubSeq(pq, 1, insert_pos-1) \o 
                  <<state>> \o 
                  SubSeq(pq, insert_pos, Len(pq))
    IN new_pq

RECURSIVE InsertBatch(_, _)
InsertBatch(pq, states_seq) ==
    IF Len(states_seq) = 0 THEN pq
    ELSE InsertBatch(PQInsert(pq, Head(states_seq)), Tail(states_seq))

PQPop(pq) ==
    [state |-> Head(pq),
     remaining |-> Tail(pq)]

-----------------------------------------------------------------------------
(* STATE SIGNATURE                                                          *)
-----------------------------------------------------------------------------

StateSignature(state) ==
    [resources |-> state.resource_state,
     statuses |-> state.thread_status_state,
     queues |-> state.waiting_queues_state]

AlreadyExplored(state) ==
    StateSignature(state) \in explored_set

-----------------------------------------------------------------------------
(* INITIAL STATE                                                            *)
-----------------------------------------------------------------------------

KiDporInit ==
    /\ Init  
    /\ LET initial_state == [
           path |-> <<>>,
           cost_g |-> 0,
           heuristic_h |-> Heuristic([
               path |-> <<>>,
               resource_state |-> resources,
               waiting_queues_state |-> waiting_queues,
               thread_status_state |-> thread_status,
               clock_state |-> [t1 \in Threads |-> [t2 \in Threads |-> 0]]
           ]),
           priority_f |-> 0,
           resource_state |-> resources,
           waiting_queues_state |-> waiting_queues,
           thread_status_state |-> thread_status,
           blocked_on_state |-> blocked_on, (* Init from ResourceOracle *)
           wfg_state |-> wait_for_graph,    (* Init from ResourceOracle *)
           clock_state |-> [t1 \in Threads |-> [t2 \in Threads |-> 0]]
       ]
       IN /\ priority_queue = <<initial_state>>
          /\ explored_set = {}
          /\ current_state = initial_state
          /\ stats = [explored |-> 0, queue_max |-> 1, expansions |-> 0]

-----------------------------------------------------------------------------
(* STATE TRANSITION LOGIC (NextSnapshot)                                    *)
-----------------------------------------------------------------------------

(****************************************************************************)
(* [FIX] NextSnapshot: blocked_on과 wfg까지 완벽하게 업데이트               *)
(****************************************************************************)
NextSnapshot(curr, t, op, r) ==
    IF op = "Request" THEN
        IF curr.resource_state[r].owner = Null THEN
            (* Acquire: No blocking *)
            [res |-> [curr.resource_state EXCEPT ![r] = [owner |-> t, count |-> 1]],
             q   |-> curr.waiting_queues_state,
             sts |-> curr.thread_status_state,
             blk |-> curr.blocked_on_state,
             wfg |-> curr.wfg_state]
        ELSE IF curr.resource_state[r].owner = t THEN
             (* Re-entrant *)
             [res |-> curr.resource_state, 
              q |-> curr.waiting_queues_state, 
              sts |-> curr.thread_status_state,
              blk |-> curr.blocked_on_state,
              wfg |-> curr.wfg_state]
        ELSE
            (* Block: Update blocked_on and Wait-For-Graph *)
            LET owner == curr.resource_state[r].owner IN
            [res |-> curr.resource_state,
             q   |-> [curr.waiting_queues_state EXCEPT ![r] = Append(@, t)],
             sts |-> [curr.thread_status_state EXCEPT ![t] = "Blocked"],
             blk |-> [curr.blocked_on_state EXCEPT ![t] = r],
             wfg |-> [curr.wfg_state EXCEPT ![t] = {owner}]]
    ELSE (* Release *)
        IF curr.resource_state[r].owner # t THEN
             (* Error *)
             [res |-> curr.resource_state, 
              q |-> curr.waiting_queues_state, 
              sts |-> curr.thread_status_state,
              blk |-> curr.blocked_on_state,
              wfg |-> curr.wfg_state]
        ELSE IF curr.waiting_queues_state[r] = <<>> THEN
            (* Free *)
            [res |-> [curr.resource_state EXCEPT ![r] = [owner |-> Null, count |-> 0]],
             q   |-> curr.waiting_queues_state,
             sts |-> curr.thread_status_state,
             blk |-> curr.blocked_on_state,
             wfg |-> curr.wfg_state]
        ELSE
            (* Wake Up: Clear blockage for next thread *)
            LET next_t == Head(curr.waiting_queues_state[r]) IN
            [res |-> [curr.resource_state EXCEPT ![r] = [owner |-> next_t, count |-> 1]],
             q   |-> [curr.waiting_queues_state EXCEPT ![r] = Tail(@)],
             sts |-> [curr.thread_status_state EXCEPT ![next_t] = "Running"],
             blk |-> [curr.blocked_on_state EXCEPT ![next_t] = Null],
             wfg |-> [curr.wfg_state EXCEPT ![next_t] = {}]]

-----------------------------------------------------------------------------
(* SUCCESSOR GENERATION (A* Expansion)                                      *)
-----------------------------------------------------------------------------

EnabledThreads(state) ==
    {t \in Threads : state.thread_status_state[t] = "Running"}

ExpandState ==
    /\ ~PQEmpty
    /\ LET popped == PQPop(priority_queue)
           curr == popped.state
           remaining_pq == popped.remaining
           
           possible_steps == {
               [thread |-> t, op |-> op, resource |-> r] :
               t \in EnabledThreads(curr),
               op \in Operations,
               r \in Resources
           }
           
           steps_seq == SetToSeq(possible_steps)
           
           successors == [i \in 1..Len(steps_seq) |-> 
               LET step_info == steps_seq[i]
                   t == step_info.thread
                   op == step_info.op
                   r == step_info.resource
                   
                   next_snap == NextSnapshot(curr, t, op, r)
                   new_depth == Len(curr.path) + 1
                   
                   new_step_rec == [thread |-> t, op |-> op, 
                                    resource |-> r, depth |-> Len(curr.path)]
                   new_path == Append(curr.path, new_step_rec)
                   new_g == curr.cost_g + 1
                   
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
                       clock_state |-> curr.clock_state
                   ]
                   new_h == Heuristic(new_state)
                   new_f == ComputePriority(new_g, new_h)
                   
                   final_state == [new_state EXCEPT 
                       !.heuristic_h = new_h,
                       !.priority_f = new_f]
               IN final_state
           ]
           
           new_pq == InsertBatch(remaining_pq, successors)

       IN
           /\ current_state' = curr
           /\ explored_set' = explored_set \cup {StateSignature(curr)}
           /\ priority_queue' = new_pq
           /\ stats' = [stats EXCEPT 
                !.explored = @ + 1,
                !.expansions = @ + 1,
                !.queue_max = IF Len(new_pq) > @ THEN Len(new_pq) ELSE @]
           
           (* [FIX] Update ALL ResourceOracle variables to match *)
           /\ resources' = curr.resource_state
           /\ waiting_queues' = curr.waiting_queues_state
           /\ thread_status' = curr.thread_status_state
           /\ blocked_on' = curr.blocked_on_state
           /\ wait_for_graph' = curr.wfg_state
           /\ UNCHANGED <<current_time, execution_history, visited_pcs>>

-----------------------------------------------------------------------------
(* ACTIONS & SPEC                                                           *)
-----------------------------------------------------------------------------

KiNext ==
    \/ ExpandState
    \/ (PQEmpty /\ UNCHANGED <<all_vars>>) 

KiSpec == KiDporInit /\ [][KiNext]_all_vars

-----------------------------------------------------------------------------
(* INVARIANTS & PROPERTIES                                                  *)
-----------------------------------------------------------------------------

KiTypeOK ==
    /\ priority_queue \in Seq(ExecutionState)
    /\ explored_set \in SUBSET [resources: [Resources -> ResourceState], 
                               statuses: [Threads -> ThreadStatusValues], 
                               queues: [Resources -> Seq(Threads)]]
    /\ current_state \in ExecutionState
    /\ TypeOK 

QueueSorted ==
    \A i, j \in DOMAIN priority_queue :
        i < j => priority_queue[i].priority_f <= priority_queue[j].priority_f

SafetyPreserved ==
    /\ NoDeadlock
    /\ MutualExclusion
    /\ NoOrphanedWaiters

Completeness ==
    <>(\A s \in explored_set : 
        ~HasCycle \/ \E sig \in explored_set : 
            \E state : StateSignature(state) = sig /\ HasCycle)

HeuristicAdmissible ==
    \A state \in ExecutionState :
        state.heuristic_h <= MaxDepth

QueueBounded ==
    stats.queue_max <= MaxDepth * Cardinality(Threads) * 10 

EfficientExploration ==
    <>[] (stats.explored < (Cardinality(Threads) ^ MaxDepth))

-----------------------------------------------------------------------------
(* SPECIFICATION                                                            *)
-----------------------------------------------------------------------------

Fairness ==
    /\ WF_all_vars(ExpandState)

FairSpec == KiSpec /\ Fairness

CurrentTime == current_time <= 20
StatsExplored == stats.explored <= 20

===============================================================================