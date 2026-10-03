----------------------------- MODULE TwoPhaseCommit -----------------------------

CONSTANTS
  RM,   \* Set of resource managers
  r2    \* A distinguished resource manager; assumed to be in RM

ASSUME r2 \in RM

(*
  RM states:
    "working"   - actively processing the transaction
    "prepared"  - voted yes; ready to commit
    "committed" - decided to commit
    "aborted"   - decided to abort
*)
RMState == {"working", "prepared", "committed", "aborted"}

VARIABLES rmState

Init ==
  rmState = [r \in RM |-> "working"]

AllPrepared ==
  /\ \A r \in RM: rmState[r] \in {"prepared", "committed"}

Prepare(r) ==
  /\ r \in RM
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

Commit(r) ==
  /\ r \in RM
  /\ rmState[r] = "prepared"
  /\ AllPrepared
  /\ rmState' = [rmState EXCEPT ![r] = "committed"]

Abort(r) ==
  /\ r \in RM
  /\ rmState[r] \in {"working", "prepared"}
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

Decide(r) ==
  Commit(r) \/ Abort(r)

Next ==
  \E r \in RM: Prepare(r) \/ Decide(r)

TCSpec ==
  Init /\ [][Next]_rmState

TCTypeOK ==
  rmState \in [RM -> RMState]

TCConsistent ==
  ~(\E r \in RM: \E s \in RM:
       rmState[r] = "committed" /\ rmState[s] = "aborted")

=============================================================================