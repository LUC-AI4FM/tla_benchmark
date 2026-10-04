---------------------------- MODULE LockWithHistory ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Procs

VARIABLES pc, h_turn, s

vars == <<pc, h_turn, s>>

--------------------------------------------------------------------------------
(* Process control states *)
(* 
   To mimic Peterson's three-step entry protocol:
   - "idle": not trying to enter critical section
   - "step1": first step of entry protocol (set flag)
   - "step2": second step of entry protocol (set turn)
   - "step3": third step of entry protocol (wait)
   - "cs": in critical section
   - "exit": leaving critical section
*)

States == {"idle", "step1", "step2", "step3", "cs", "exit"}

--------------------------------------------------------------------------------
(* Type invariant *)
TypeOK ==
    /\ pc \in [Procs -> States]
    /\ h_turn \in Procs \cup {CHOOSE x : x \notin Procs}
    /\ s \in [Procs -> 0..2]

(* Initial state *)
Init ==
    /\ pc = [p \in Procs |-> "idle"]
    /\ h_turn = CHOOSE x : x \notin Procs
    /\ s = [p \in Procs |-> 0]

--------------------------------------------------------------------------------
(* Transition actions *)

(* Process p begins trying to enter critical section - step 1 of entry *)
TryEnter1(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "step1"]
    /\ s' = [s EXCEPT ![p] = 0]
    /\ UNCHANGED h_turn

(* Process p continues entry protocol - step 2 *)
TryEnter2(p) ==
    /\ pc[p] = "step1"
    /\ pc' = [pc EXCEPT ![p] = "step2"]
    /\ s' = [s EXCEPT ![p] = 1]
    /\ UNCHANGED h_turn

(* Process p sets turn and moves to step 3 - records history *)
TryEnter3(p) ==
    /\ pc[p] = "step2"
    /\ pc' = [pc EXCEPT ![p] = "step3"]
    /\ h_turn' = p
    /\ s' = [s EXCEPT ![p] = 2]

(* Process p enters critical section if allowed *)
EnterCS(p) ==
    /\ pc[p] = "step3"
    /\ \/ \A q \in Procs \ {p} : pc[q] \in {"idle", "exit"}
       \/ h_turn # p
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ UNCHANGED <<h_turn, s>>

(* Process p exits critical section *)
ExitCS(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ UNCHANGED <<h_turn, s>>

(* Process p returns to idle *)
ReturnToIdle(p) ==
    /\ pc[p] = "exit"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ s' = [s EXCEPT ![p] = 0]
    /\ UNCHANGED h_turn

(* Stuttering step for process p - allows additional stuttering to match Peterson *)
Stutter(p) ==
    /\ s[p] < 2
    /\ pc[p] \in {"step1", "step2", "step3"}
    /\ UNCHANGED <<pc, h_turn>>
    /\ s' = s

--------------------------------------------------------------------------------
(* Next state relation *)
Next ==
    \E p \in Procs :
        \/ TryEnter1(p)
        \/ TryEnter2(p)
        \/ TryEnter3(p)
        \/ EnterCS(p)
        \/ ExitCS(p)
        \/ ReturnToIdle(p)
        \/ Stutter(p)

--------------------------------------------------------------------------------
(* Fairness conditions *)
Fairness ==
    \A p \in Procs :
        /\ WF_vars(TryEnter1(p))
        /\ WF_vars(TryEnter2(p))
        /\ WF_vars(TryEnter3(p))
        /\ WF_vars(EnterCS(p))
        /\ WF_vars(ExitCS(p))
        /\ WF_vars(ReturnToIdle(p))

--------------------------------------------------------------------------------
(* Specification *)
Spec == Init /\ [][Next]_vars /\ Fairness

--------------------------------------------------------------------------------
(* Safety Invariants *)

(* Mutual exclusion: at most one process in critical section *)
MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

(* The history variable correctly tracks who last set turn *)
HistoryConsistency ==
    \A p \in Procs :
        (pc[p] \in {"step3", "cs"} /\ s[p] = 2) =>
            (h_turn \in Procs)

(* Stuttering counter bounds *)
StutterBound ==
    \A p \in Procs : s[p] \in 0..2

--------------------------------------------------------------------------------
(* Liveness Properties *)

(* Every process that tries to enter eventually enters *)
Liveness ==
    \A p \in Procs : pc[p] = "step1" ~> pc[p] = "cs"

(* Starvation freedom *)
StarvationFreedom ==
    \A p \in Procs : pc[p] # "idle" ~> pc[p] = "cs"

--------------------------------------------------------------------------------
(* Refinement mapping to Peterson's algorithm *)
(* 
   The following defines how this specification maps to Peterson's:
   - flag[p] is true iff pc[p] \notin {"idle", "exit"}
   - turn corresponds to h_turn
   - Peterson's pc states map to our extended states
*)

PetersonFlag == [p \in Procs |-> pc[p] \notin {"idle", "exit"}]
PetersonTurn == h_turn
PetersonPC == [p \in Procs |-> 
    CASE pc[p] = "idle" -> "ncs"
      [] pc[p] \in {"step1", "step2", "step3"} -> "wait"
      [] pc[p] = "cs" -> "cs"
      [] pc[p] = "exit" -> "exit"
      [] OTHER -> "ncs"]

================================================================================