---------------------------- MODULE TwoPhaseCommit ----------------------------

CONSTANT RM

VARIABLE rmState

States == {"working", "prepared", "committed", "aborted"}

Init ==
  rmState = [ r \in RM |-> "working" ]

AllPrepared ==
  \A r \in RM: rmState[r] \in {"prepared", "committed"}

AllCommitted ==
  \A r \in RM: rmState[r] = "committed"

Prepare(r) ==
  /\ r \in RM
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

Commit(r) ==
  /\ r \in RM
  /\ rmState[r] = "prepared"
  /\ AllPrepared
  /\ rmState' = [rmState EXCEPT ![r] = "committed"]

AbortFromWorking(r) ==
  /\ r \in RM
  /\ rmState[r] = "working"
  /\ ~AllPrepared
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

AbortFromPrepared(r) ==
  /\ r \in RM
  /\ rmState[r] = "prepared"
  /\ ~AllPrepared
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

Next ==
  \E r \in RM:
       Prepare(r)
    \/ Commit(r)
    \/ AbortFromWorking(r)
    \/ AbortFromPrepared(r)

TCSpec ==
  Init /\ [][Next]_rmState

TCTypeOK ==
  rmState \in [RM -> States]

TCConsistent ==
  ~(\E r1 \in RM, r2 \in RM:
       rmState[r1] = "committed" /\ rmState[r2] = "aborted")

CommitSome ==
  \E r \in RM: Commit(r)

r2 ==
  AllPrepared => (AllCommitted \/ ENABLED CommitSome)

=============================================================================