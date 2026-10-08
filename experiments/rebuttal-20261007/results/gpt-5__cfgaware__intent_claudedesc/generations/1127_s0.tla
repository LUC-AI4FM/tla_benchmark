----------------------------- MODULE SinglePhaseCommit -----------------------------

EXTENDS TLC

CONSTANTS  \* None required; all definitions are concrete in this module.

(*
  Fixed set of three resource managers and a distinguished element r2.
*)
RM == {"r1", "r2", "r3"}
r2 == "r2"

(*
  Phases of a resource manager.
*)
Phases == {"working", "prepared", "committed", "aborted"}

VARIABLE rmState

Init ==
  rmState = [r \in RM |-> "working"]

AllPrepared ==
  \A r \in RM: rmState[r] \in {"prepared", "committed"}

NoCommitYet ==
  \A r \in RM: rmState[r] # "committed"

Prepare(r) ==
  /\ r \in RM
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

Abort(r) ==
  /\ r \in RM
  /\ rmState[r] \in {"working", "prepared"}
  /\ NoCommitYet
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

Commit(r) ==
  /\ r \in RM
  /\ rmState[r] = "prepared"
  /\ AllPrepared
  /\ rmState' = [rmState EXCEPT ![r] = "committed"]

Next ==
  \E r \in RM:
      Prepare(r)
    \/ Abort(r)
    \/ Commit(r)

TCSpec ==
  Init /\ [][Next]_rmState

(*
  Safety properties:
  - Type correctness: every RM is always in one of the four phases.
  - Consistency: it is never the case that some RM is committed while another is aborted.
*)
TCTypeOK ==
  rmState \in [RM -> Phases]

TCConsistent ==
  ~(\E c \in RM: rmState[c] = "committed") \/ ~(\E a \in RM: rmState[a] = "aborted")

=============================================================================