------------------------------ MODULE TCommit ------------------------------
(***************************************************************************)
(* Transaction commit protocol for a set RM of resource managers.          *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT RM       \* The set of participating resource managers

VARIABLE rmState  \* rmState[rm] is the state of resource manager rm

vars == <<rmState>>

TCTypeOK ==
  rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

TCInit == rmState = [rm \in RM |-> "working"]

canCommit == \A rm \in RM : rmState[rm] \in {"prepared", "committed"}
  \* True iff all RMs are in the "prepared" or "committed" state.

notCommitted == \A rm \in RM : rmState[rm] # "committed"
  \* True iff no resource manager has decided to commit.

Prepare(rm) ==
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]

Decide(rm) ==
  \/ /\ rmState[rm] = "prepared"
     /\ canCommit
     /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
  \/ /\ rmState[rm] \in {"working", "prepared"}
     /\ notCommitted
     /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]

TCNext == \E rm \in RM : Prepare(rm) \/ Decide(rm)

TCSpec == TCInit /\ [][TCNext]_rmState

-----------------------------------------------------------------------------
(* Safety: no RM commits while another has aborted, and vice versa. *)
TCConsistent ==
  \A rm1, rm2 \in RM : ~ /\ rmState[rm1] = "aborted"
                         /\ rmState[rm2] = "committed"

(* An RM can only be committed if all RMs are prepared or committed. *)
CommitOnlyIfAllPrepared ==
  (\E rm \in RM : rmState[rm] = "committed") => canCommit

THEOREM TCSpec => [](TCTypeOK /\ TCConsistent /\ CommitOnlyIfAllPrepared)
=============================================================================