------------------------------ MODULE TwoPhaseCommit ------------------------------
EXTENDS TLC

CONSTANT RM

VARIABLE rmState

(* --type definitions-- *)
RMStates == {"working", "prepared", "committed", "aborted"}

(* --initialization-- *)
Init ==
  /\ rmState \in [RM -> RMStates]
  /\ \A r \in RM : rmState[r] = "working"

(* --action definitions-- *)
Prepare(r) ==
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

AllPrepared == \A r \in RM : rmState[r] \in {"prepared", "committed"}

Commit(r) ==
  /\ rmState[r] = "prepared"
  /\ AllPrepared
  /\ rmState' = [rmState EXCEPT ![r] = "committed"]

NoCommitted == \A r \in RM : rmState[r] # "committed"

Abort(r) ==
  /\ rmState[r] \in {"working", "prepared"}
  /\ NoCommitted
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

TCNext ==
  \E r \in RM :
    Prepare(r)
    \/ Commit(r)
    \/ Abort(r)

(* --specification-- *)
Spec == Init /\ [] (TCNext \/ Stutter)

(* --invariants-- *)
TCTypeOK == rmState \in [RM -> RMStates]

TCConsistent ==
  \A r1, r2 \in RM : ~(rmState[r1] = "aborted" /\ rmState[r2] = "committed")

=============================================================================