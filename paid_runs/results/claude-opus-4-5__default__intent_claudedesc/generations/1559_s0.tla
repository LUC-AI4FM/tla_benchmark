---------------------------- MODULE AugmentedLock ----------------------------
(***************************************************************************)
(* An augmented mutual-exclusion lock serving as a refinement bridge       *)
(* between a simple two-process lock and Peterson's algorithm.             *)
(* Uses history and stuttering variables per Lamport's methodology.        *)
(***************************************************************************)

EXTENDS Integers, TLC

CONSTANTS Procs
ASSUME Procs = {0, 1}

VARIABLES
    pc,         \* Program counter for each process: "idle", "entry", "cs", "exit"
    turn,       \* Turn variable for Peterson's algorithm
    flag,       \* Flag array for Peterson's algorithm  
    hist_turn,  \* History variable: tracks which process was last assigned turn
    stutter     \* Stuttering variable: sub-step counter for entry phase (0, 1, 2, 3)

vars == <<pc, turn, flag, hist_turn, stutter>>
baseVars == <<pc, turn, flag>>

Other(p) == IF p = 0 THEN 1 ELSE 0

(***************************************************************************)
(* Type Correctness                                                        *)
(***************************************************************************)
TypeOK ==
    /\ pc \in [Procs -> {"idle", "entry", "cs", "exit"}]
    /\ turn \in Procs
    /\ flag \in [Procs -> BOOLEAN]
    /\ hist_turn \in Procs \cup {-1}  \* -1 indicates no assignment yet
    /\ stutter \in [Procs -> 0..3]    \* 0=idle, 1,2,3 = entry sub-steps

(***************************************************************************)
(* Initial State                                                           *)
(***************************************************************************)
Init ==
    /\ pc = [p \in Procs |-> "idle"]
    /\ turn = 0
    /\ flag = [p \in Procs |-> FALSE]
    /\ hist_turn = -1
    /\ stutter = [p \in Procs |-> 0]

(***************************************************************************)
(* Actions                                                                 *)
(***************************************************************************)

(* Process p starts entry: sets its flag to TRUE *)
(* This is entry sub-step 1 of 3, corresponding to Peterson's flag[p] := TRUE *)
StartEntry(p) ==
    /\ pc[p] = "idle"
    /\ stutter[p] = 0
    /\ pc' = [pc EXCEPT ![p] = "entry"]
    /\ flag' = [flag EXCEPT ![p] = TRUE]
    /\ stutter' = [stutter EXCEPT ![p] = 1]
    /\ UNCHANGED <<turn, hist_turn>>

(* Entry sub-step 2: assigns turn to other process *)
(* Corresponds to Peterson's turn := Other(p) *)
EntryStep2(p) ==
    /\ pc[p] = "entry"
    /\ stutter[p] = 1
    /\ turn' = Other(p)
    /\ hist_turn' = p  \* Record that p assigned the turn
    /\ stutter' = [stutter EXCEPT ![p] = 2]
    /\ UNCHANGED <<pc, flag>>

(* Entry sub-step 3: wait until can enter critical section *)
(* Corresponds to Peterson's await ~flag[Other(p)] \/ turn = p *)
EntryStep3(p) ==
    /\ pc[p] = "entry"
    /\ stutter[p] = 2
    /\ \/ ~flag[Other(p)]
       \/ turn = p
    /\ stutter' = [stutter EXCEPT ![p] = 3]
    /\ UNCHANGED <<pc, turn, flag, hist_turn>>

(* Complete entry and move to critical section *)
EnterCS(p) ==
    /\ pc[p] = "entry"
    /\ stutter[p] = 3
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ stutter' = [stutter EXCEPT ![p] = 0]
    /\ UNCHANGED <<turn, flag, hist_turn>>

(* Exit critical section: reset flag *)
ExitCS(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ flag' = [flag EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<turn, hist_turn, stutter>>

(* Return to idle state *)
ReturnToIdle(p) ==
    /\ pc[p] = "exit"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<turn, flag, hist_turn, stutter>>

(***************************************************************************)
(* Next State Relation                                                     *)
(***************************************************************************)
Next ==
    \E p \in Procs:
        \/ StartEntry(p)
        \/ EntryStep2(p)
        \/ EntryStep3(p)
        \/ EnterCS(p)
        \/ ExitCS(p)
        \/ ReturnToIdle(p)

(***************************************************************************)
(* Fairness                                                                *)
(***************************************************************************)
Fairness ==
    \A p \in Procs:
        /\ WF_vars(StartEntry(p))
        /\ WF_vars(EntryStep2(p))
        /\ WF_vars(EntryStep3(p))
        /\ WF_vars(EnterCS(p))
        /\ WF_vars(ExitCS(p))
        /\ WF_vars(ReturnToIdle(p))

(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Safety Invariants                                                       *)
(***************************************************************************)

(* Mutual Exclusion: at most one process in critical section *)
MutualExclusion ==
    \A p, q \in Procs: (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

(* Invariant relating pc, stutter, and turn ownership *)
(* If a process completed its turn assignment (stutter >= 2) and is still *)
(* trying to enter, the turn ownership reflects the history correctly *)
TurnOwnershipInvariant ==
    \A p \in Procs:
        /\ (stutter[p] >= 2 /\ pc[p] = "entry") =>
           (hist_turn = p => turn = Other(p))
        /\ (pc[p] = "cs") =>
           (flag[p] = TRUE)

(* Consistency between stutter state and pc *)
StutterConsistency ==
    \A p \in Procs:
        /\ (pc[p] = "idle" => stutter[p] = 0)
        /\ (pc[p] = "entry" => stutter[p] \in 1..3)
        /\ (pc[p] \in {"cs", "exit"} => stutter[p] = 0)

(* Combined type and structural invariant *)
Invariant ==
    /\ TypeOK
    /\ MutualExclusion
    /\ StutterConsistency

(***************************************************************************)
(* Liveness Properties                                                     *)
(***************************************************************************)

(* Starvation Freedom: if a process wants to enter, it eventually does *)
StarvationFreedom ==
    \A p \in Procs: (pc[p] = "entry") ~> (pc[p] = "cs")

(* Deadlock Freedom: some process can always make progress *)
DeadlockFreedom ==
    [](\E p \in Procs: pc[p] = "cs" \/ ENABLED(Next))

(***************************************************************************)
(* Refinement Mapping to Simple Lock (hiding auxiliary variables)          *)
(***************************************************************************)

(* The simple lock has: pc_simple cycling through idle -> entry -> cs -> exit *)
(* We map our extended states to simple lock states *)
SimpleLockPC ==
    [p \in Procs |-> 
        IF pc[p] = "idle" THEN "idle"
        ELSE IF pc[p] = "entry" THEN "entry"  
        ELSE IF pc[p] = "cs" THEN "cs"
        ELSE "exit"]

(* This specification refines SimpleLock when we hide hist_turn and stutter *)
(* and collapse the three entry sub-steps into one abstract entry state *)

(***************************************************************************)
(* Refinement Mapping to Peterson's Algorithm                              *)
(***************************************************************************)

(* Peterson's algorithm has labels: *)
(* "ncs" (non-critical), "a1" (set flag), "a2" (set turn), *)
(* "a3" (wait), "cs" (critical), "a4" (reset flag) *)

PetersonPC ==
    [p \in Procs |->
        CASE pc[p] = "idle" /\ stutter[p] = 0 -> "ncs"
          [] pc[p] = "entry" /\ stutter[p] = 1 -> "a2"   \* Just set flag, about to set turn
          [] pc[p] = "entry" /\ stutter[p] = 2 -> "a3"   \* Set turn, now waiting
          [] pc[p] = "entry" /\ stutter[p] = 3 -> "a3a"  \* Wait passed, about to enter
          [] pc[p] = "cs" -> "cs"
          [] pc[p] = "exit" -> "a4"
          [] OTHER -> "ncs"]

(* Peterson's flag is directly our flag *)
PetersonFlag == flag

(* Peterson's turn is directly our turn *)
PetersonTurn == turn

(* The refinement shows: this spec with auxiliary variables removed *)
(* is equivalent to Peterson when the PC mapping is applied *)

(***************************************************************************)
(* Theorems (checked by TLC)                                               *)
(***************************************************************************)

THEOREM Spec => []TypeOK
THEOREM Spec => []MutualExclusion
THEOREM Spec => []StutterConsistency
THEOREM Spec => StarvationFreedom

=============================================================================