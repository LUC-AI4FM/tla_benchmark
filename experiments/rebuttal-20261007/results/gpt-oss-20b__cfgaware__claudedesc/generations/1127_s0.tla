------------------------------ MODULE TwoPhaseCommit ------------------------------
EXTENDS Naturals, TLC

CONSTANT RM, r2

VARIABLE rmState

(* The set of allowed states *)
StateSet == {"working", "prepared", "committed", "aborted"}

Init ==
  /\ rmState \in [RM -> StateSet]
  /\ \A r \in RM : rmState[r] = "working"

Prepare ==
  \E r \in RM :
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

Commit ==
  \E r \in RM :
    /\ rmState[r] = "prepared"
    /\ (\A s \in RM : rmState[s] \in {"prepared", "committed"})
    /\ rmState' = [rmState EXCEPT ![r] = "committed"]

Abort ==
  \E r \in RM :
    /\ rmState[r] \in {"working", "prepared"}
    /\ (\A s \in RM : rmState[s] # "committed")
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

Decide == Commit \/ Abort

Stutter ==
  rmState' = rmState

TCNext == Prepare \/ Decide \/ Stutter

TCSpec == Init /\ [] TCNext

(* Invariants *)
TCTypeOK ==
  rmState \in [RM -> StateSet]

TCConsistent ==
  \A r1, r2 \in RM :
    ~(rmState[r1] = "aborted" /\ rmState[r2] = "committed")

=============================================================================