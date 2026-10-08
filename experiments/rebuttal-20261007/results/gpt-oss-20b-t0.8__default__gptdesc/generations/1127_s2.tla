MODULE TwoPhaseCommitRM
EXTENDS TLC

CONSTANTS RMSet

VARIABLE rmState

States == {"working", "prepared", "committed", "aborted"}

Init ==
  /\ rmState \in [RMSet -> States]
  /\ ∀ r ∈ RMSet : rmState[r] = "working"

Prepare(r) ==
  /\ r ∈ RMSet
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

Commit(r) ==
  /\ r ∈ RMSet
  /\ rmState[r] = "prepared"
  /\ rmState' = [rmState EXCEPT ![r] = "committed"]

Abort(r) ==
  /\ r ∈ RMSet
  /\ rmState[r] = "prepared"
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

Next == ∃ r ∈ RMSet : (Prepare(r) \/ Commit(r) \/ Abort(r))

vars == <<rmState>>

TypeOK ==
  ∀ r ∈ RMSet : rmState[r] ∈ States

Consistency ==
  ¬∃ r1, r2 ∈ RMSet :
    (rmState[r1] = "committed" /\ rmState[r2] = "aborted")

SafetyInvariant == TypeOK /\ Consistency

Spec == Init /\ [][Next]_vars

ASSERT []TypeOK
ASSERT []Consistency

END MODULE