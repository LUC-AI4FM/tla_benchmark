MODULE LamportFastMutualExclusion
EXTENDS Naturals, Sequences, TLC, SETS

CONSTANT N

VARIABLES x, y, b, failed, csSet, procState

(* --algorithm initialization ------------------------------------------------- *)
Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in 1..N |-> FALSE]
  /\ failed = [i \in 1..N |-> FALSE]
  /\ csSet = {}
  /\ procState = [i \in 1..N |-> "idle"]

(* --process actions ----------------------------------------------------------- *)
RaiseFlag(i) ==
  /\ i \in 1..N
  /\ procState[i] = "idle"
  /\ b' = [b EXCEPT ![i] = TRUE]
  /\ x' = i
  /\ procState'[i] = "flagRaised"

CheckY(i) ==
  /\ i \in 1..N
  /\ procState[i] = "flagRaised"
  /\ y #= 0
  /\ y' = i
  /\ procState'[i] = "writeX"

EnterCSAfterWriteY(i) ==
  /\ i \in 1..N
  /\ procState[i] = "writeX"
  /\ x = i
  /\ csSet' = csSet ∪ {i}
  /\ procState'[i] = "inCS"

ClearFlagAndWaitOthers(i) ==
  /\ i \in 1..N
  /\ procState[i] = "writeX"
  /\ x #= i
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ procState'[i] = "waitOthers"

WaitForOthersClear(i) ==
  /\ i \in 1..N
  /\ procState[i] = "waitOthers"
  /\ ∀j \in 1..N : (j #= i) => b[j] = FALSE
  /\ procState'[i] = "checkYAgain"

EnterCSAfterCheckY(i) ==
  /\ i \in 1..N
  /\ procState[i] = "checkYAgain"
  /\ y = i
  /\ csSet' = csSet ∪ {i}
  /\ procState'[i] = "inCS"

WaitForYZero(i) ==
  /\ i