------------------------------ MODULE FastMutualExclusion ------------------------------
EXTENDS Naturals

CONSTANT N
PROC == 1..N

(* State labels *)
StateNC          == 0
StateIntentSet   == 1
StateXAssigned   == 2
StateYZeroTest   == 3
StateCheckBYFalse== 4
StateCritical    == 5

VARIABLES pc, b, x, y

vars == <<pc, b, x, y>>

(* Initial condition *)
Init ==
  /\ \A i \in PROC : pc[i] = StateNC
  /\ \A i \in PROC : b[i] = FALSE
  /\ x = 0
  /\ y = 0

(* Actions for each process *)
NonCritical(i) ==
  /\ pc[i] = StateNC
  /\ pc' = [pc EXCEPT ![i] = StateIntentSet]
  /\ UNCHANGED <<b, x, y>>

SetIntent(i) ==
  /\ pc[i] = StateIntentSet
  /\ b' = [b EXCEPT ![i] = TRUE]
  /\ pc' = [pc EXCEPT ![i] = StateXAssigned]
  /\ UNCHANGED <<x, y>>

AssignX(i) ==
  /\ pc[i] = StateXAssigned
  /\ x' = i
  /\ pc' = [pc EXCEPT ![i] = StateYZeroTest]
  /\ UNCHANGED <<b, y>>

YZeroSet(i) ==
  /\ pc[i] = StateYZeroTest
  /\ y = 0
  /\ y' = i
  /\ pc' = [pc EXCEPT ![i] = StateCheckBYFalse]
  /\ UNCHANGED <<b, x>>

WaitYNonZero(i) ==
  /\ pc[i] = StateYZeroTest
  /\ y # 0
  /\ UNCHANGED <<pc, b, x, y>>

CheckByFalseTrue(i) ==
  /\ pc[i] = StateCheckBYFalse
  /\ b[y] = FALSE
  /\ pc' = [pc EXCEPT ![i] = StateCritical]
  /\ UNCHANGED <<b, x, y>>

WaitForYZero(i) ==
  /\ pc[i] = StateCheckBYFalse
  /\ b[y] = TRUE
  /\ y # 0
  /\ UNCHANGED <<pc, b, x, y>>

RestartIntent(i) ==
  /\ pc[i] = StateCheckBYFalse
  /\ b[y] = TRUE
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = StateIntentSet]
  /\ UNCHANGED <<b, x, y>>

CriticalSkip(i) ==
  /\ pc[i] = StateCritical
  /\ UNCHANGED <<pc, b, x, y>>

ExitCritical(i) ==
  /\ pc[i] = StateCritical
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = StateNC]
  /\ UNCHANGED <<x, y>>

(* Next-state relation *)
Next == ∃ i \