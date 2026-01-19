---------------------------- MODULE ClassicDPOR --------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC, ResourceOracle

(****************************************************************************)
(* [FIX] EXTENDS ResourceOracle을 사용하여 상수와 변수를 상속받았습니다.    *)
(* INSTANCE 대신 EXTENDS를 쓰면 Threads, Resources 등이 바로 인식됩니다.    *)
(****************************************************************************)

-----------------------------------------------------------------------------
(* CONSTANTS - Configuration Parameters                                     *)
-----------------------------------------------------------------------------

CONSTANTS
    MaxDepth,          \* Maximum exploration depth
    Operations         \* Set of possible operations (e.g., {"Request", "Release"})

ASSUME
    /\ MaxDepth \in Nat
    /\ MaxDepth > 0
    /\ Operations # {}

-----------------------------------------------------------------------------
(* DPOR STATE VARIABLES                                                     *)
-----------------------------------------------------------------------------

VARIABLES
    stack,             
    current_depth,    
    backtrack_sets,   
    done_sets,        
    clock_vectors,    
    explored_states,  
    pruned_states     

dpor_vars == <<stack, current_depth, backtrack_sets, done_sets, 
               clock_vectors, explored_states, pruned_states>>

(****************************************************************************)
(* [FIX] all_vars 정의 수정                                                 *)
(* ResourceOracle의 변수(vars)와 DPOR 변수를 합칩니다.                      *)
(****************************************************************************)
all_vars == <<dpor_vars, vars>>

-----------------------------------------------------------------------------
(* TYPE DEFINITIONS                                                         *)
-----------------------------------------------------------------------------

StepRecord == [
    thread: Threads,
    op: Operations,
    resource: Resources,
    depth: Nat,
    clock: [Threads -> Nat]
]

DporTypeOK ==
    /\ stack \in Seq(StepRecord)
    /\ Len(stack) <= MaxDepth
    /\ current_depth \in 0..MaxDepth
    /\ backtrack_sets \in [0..MaxDepth -> SUBSET Threads]
    /\ done_sets \in [0..MaxDepth -> SUBSET Threads]
    /\ clock_vectors \in [Threads -> [Threads -> Nat]]
    /\ explored_states \in Nat
    /\ pruned_states \in Nat
    /\ TypeOK  \* ResourceOracle의 TypeOK

-----------------------------------------------------------------------------
(* INITIAL STATE                                                            *)
-----------------------------------------------------------------------------

DporInit ==
    /\ Init  \* ResourceOracle의 Init 호출
    /\ stack = <<>>
    /\ current_depth = 0
    /\ backtrack_sets = [d \in 0..MaxDepth |-> 
                            IF d = 0 THEN Threads ELSE {}]
    /\ done_sets = [d \in 0..MaxDepth |-> {}]
    /\ clock_vectors = [t1 \in Threads |-> [t2 \in Threads |-> 0]]
    /\ explored_states = 0
    /\ pruned_states = 0

-----------------------------------------------------------------------------
(* DEPENDENCY ANALYSIS                                                      *)
-----------------------------------------------------------------------------

IsDependentOp(step1, step2) ==
    /\ step1.resource = step2.resource
    /\ step1.thread # step2.thread
    /\ \/ step1.op = "Request" /\ step2.op = "Request"
       \/ step1.op = "Request" /\ step2.op = "Release"
       \/ step1.op = "Release" /\ step2.op = "Request"
       \/ step1.op = "Release" /\ step2.op = "Release"

HappensBefore(step1, step2) ==
    LET allLessOrEqual == \A t \in Threads : step1.clock[t] <= step2.clock[t]
        someStrictlyLess == \E t \in Threads : step1.clock[t] < step2.clock[t]
    IN allLessOrEqual /\ someStrictlyLess

IsConcurrent(step1, step2) ==
    /\ ~HappensBefore(step1, step2)
    /\ ~HappensBefore(step2, step1)

NeedBacktrack(past_step, current_step, past_depth) ==
    /\ IsDependentOp(past_step, current_step)
    /\ IsConcurrent(past_step, current_step)
    /\ current_step.thread \notin done_sets[past_depth]

-----------------------------------------------------------------------------
(* BACKTRACK SET MANAGEMENT                                                *)
-----------------------------------------------------------------------------

UpdateBacktrackSets(current_step) ==
    [d \in 0..MaxDepth |->
        IF d < Len(stack) THEN
            LET past_step == stack[d + 1]
            IN IF NeedBacktrack(past_step, current_step, d)
               THEN backtrack_sets[d] \cup {current_step.thread}
               ELSE backtrack_sets[d]
        ELSE backtrack_sets[d]
    ]

-----------------------------------------------------------------------------
(* ACTIONS                                                                  *)
-----------------------------------------------------------------------------

SchedulerStep ==
    /\ current_depth < MaxDepth
    /\ Len(stack) = current_depth
    
    /\ LET available == backtrack_sets[current_depth] \ done_sets[current_depth]
       IN available # {}
          /\ \E t \in available :
             \E op \in Operations :
             \E r \in Resources :
                LET
                    new_step == [
                        thread |-> t,
                        op |-> op,
                        resource |-> r,
                        depth |-> current_depth,
                        clock |-> clock_vectors[t]
                    ]
                    
                    new_clocks == [clock_vectors EXCEPT 
                        ![t][t] = @ + 1
                    ]
                    
                    new_backtrack_sets == UpdateBacktrackSets(new_step)
                IN
                    \* Execute ResourceOracle Action
                    /\ IF op = "Request"
                       THEN RequestResource(t, r)
                       ELSE ReleaseResource(t, r)
                    
                    \* Update DPOR state
                    /\ stack' = Append(stack, new_step)
                    /\ current_depth' = current_depth + 1
                    /\ backtrack_sets' = new_backtrack_sets
                    /\ done_sets' = [done_sets EXCEPT 
                        ![current_depth] = @ \cup {t}]
                    /\ clock_vectors' = new_clocks
                    /\ explored_states' = explored_states + 1
                    /\ UNCHANGED <<pruned_states>>

Backtrack ==
    /\ current_depth > 0
    /\ Len(stack) = current_depth
    /\ backtrack_sets[current_depth] \ done_sets[current_depth] = {}
    
    /\ LET prev_depth == current_depth - 1
       IN
           /\ stack' = SubSeq(stack, 1, Len(stack) - 1)
           /\ current_depth' = prev_depth
           
           /\ LET unexplored == backtrack_sets[current_depth] \ done_sets[current_depth]
                  pruned_count == Cardinality(Threads) - Cardinality(done_sets[current_depth])
              IN pruned_states' = pruned_states + pruned_count
           
           /\ UNCHANGED <<backtrack_sets, done_sets, clock_vectors, 
                          explored_states, vars>>

ExplorationComplete ==
    /\ current_depth = 0
    /\ backtrack_sets[0] \ done_sets[0] = {}
    /\ UNCHANGED <<all_vars>>

-----------------------------------------------------------------------------
(* INVARIANTS                                                               *)
-----------------------------------------------------------------------------

DporSafety ==
    /\ TypeOK
    /\ NoDeadlock
    /\ MutualExclusion
    /\ NoOrphanedWaiters

StackConsistency ==
    Len(stack) <= current_depth + 1

BacktrackSetsValid ==
    \A d \in 0..MaxDepth : backtrack_sets[d] \subseteq Threads

DoneSetsValid ==
    \A d \in 0..MaxDepth : done_sets[d] \subseteq backtrack_sets[d]

CurrentTime == current_time <= 20
ExploredStates == explored_states <= 100

-----------------------------------------------------------------------------
(* SPECIFICATION                                                            *)
-----------------------------------------------------------------------------

DporNext ==
    \/ SchedulerStep
    \/ Backtrack
    \/ ExplorationComplete

DporSpec == DporInit /\ [][DporNext]_all_vars

Fairness ==
    /\ WF_all_vars(SchedulerStep)
    /\ WF_all_vars(Backtrack)

FairSpec == DporSpec /\ Fairness

===============================================================================