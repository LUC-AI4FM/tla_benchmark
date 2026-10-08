------------------------------ MODULE FastMutualExclusion ------------------------------
EXTENDS Naturals, TLC

CONSTANT N \in Nat
ASSUME N > 0

VARIABLES x, y, b, cs

(* Types for clarity (not used by the model checker directly) *)
xType == {0} \/ (1..N)
yType == {0} \/ (1..N)

bType == [1..N -> BOOLEAN]
csType == [1..N -> {"Idle", "SetB", "WaitY0", "SetX", "WaitCond", "EnterCS"}]

(* Initial state *)
Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in 1..N |-> FALSE]
  /\ cs = [i \in 1..N |-> "Idle"]

(* Actions for each process i *)

SetB(i) ==
  /\ cs[i] = "Idle"
  /\ b' = [b EXCEPT ![i] = TRUE]
  /\ cs' = [cs EXCEPT ![i] = "SetB"]
  /\ UNCHANGED <<x, y>>

WaitY0(i) ==
  /\ cs[i] = "SetB"
  /\ y = 0
  /\ cs' = [cs EXCEPT ![i] = "SetX"]
  /\ UNCHANGED <<x, b, y>>

SetX(i) ==
  /\ cs[i] = "SetX"
  /\ x' = i
  /\ cs' = [cs EXCEPT ![i] = "WaitCond"]
  /\ UNCHANGED <<y, b>>

EnterCS(i) ==
  /\ cs[i] = "WaitCond"
  /\ y = 0
  /\ x = i
  /\ cs' = [cs EXCEPT ![i] = "EnterCS"]
  /\ UNCHANGED <<x, y, b>>

ExitCS(i) ==
  /\ cs[i] = "EnterCS"
  /\ y' = i
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ cs' = [cs EXCEPT ![i] = "Idle"]
  /\ UNCHANGED <<x>>

Next == \E i \in 1..N :
  (SetB(i) \/ WaitY0(i) \/ SetX(i) \/ EnterCS(i) \/ ExitCS(i))

(* Mutual exclusion invariant *)
MutualExcl ==
  \A i, j \in 1..N : i # j => cs[i] # "EnterCS" \/ cs[j] # "EnterCS"

(* Liveness: some process enters the critical section infinitely often *)
SomeProcessEntersInfinitelyOften ==
  \E i \in 1..N : []<>(cs[i] = "EnterCS")

Spec == Init /\ [][Next]_{x, y, b, cs} /\ WF_vars[Next]

=============================================================================