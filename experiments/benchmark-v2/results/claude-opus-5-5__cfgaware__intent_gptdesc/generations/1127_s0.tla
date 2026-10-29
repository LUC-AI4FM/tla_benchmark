------------------------------ MODULE TCommit ------------------------------
(***************************************************************************)
(* Abstract specification of the transaction commit problem for a set of   *)
(* resource managers (participants).  Each participant independently      *)
(* moves between the states "working", "prepared", "committed" and        *)
(* "aborted".  The global enabling conditions guarantee that no two        *)
(* participants reach conflicting final decisions.                         *)
(***************************************************************************)
CONSTANT RM        \* The set of participating resource managers

VARIABLE rmState   \* rmState[r] is the state of resource manager r

vars == << rmState >>

-----------------------------------------------------------------------------
States == {"working", "prepared", "committed", "aborted"}

TCTypeOK ==
  (*************************************************************************)
  (* Type invariant: every participant is in one of the four states.      *)
  (*************************************************************************)
  rmState \in [RM -> States]

TCInit ==
  (*************************************************************************)
  (* Initially every participant is in the neutral "working" state.       *)
  (*************************************************************************)
  rmState = [r \in RM |-> "working"]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Global enabling conditions.                                             *)
(***************************************************************************)
canCommit ==
  (*************************************************************************)
  (* Committing is safe once every participant is prepared or some        *)
  (* participant has already committed.                                   *)
  (*************************************************************************)
  \A r \in RM : rmState[r] \in {"prepared", "committed"}

notCommitted ==
  (*************************************************************************)
  (* Aborting is allowed only while no participant has committed.         *)
  (*************************************************************************)
  \A r \in RM : rmState[r] # "committed"

-----------------------------------------------------------------------------
(***************************************************************************)
(* Participant-local actions.                                              *)
(***************************************************************************)
Prepare(r) ==
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

Decide(r) ==
  \/ /\ rmState[r] = "prepared"
     /\ canCommit
     /\ rmState' = [rmState EXCEPT ![r] = "committed"]
  \/ /\ rmState[r] \in {"working", "prepared"}
     /\ notCommitted
     /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

TCNext == \E r \in RM : Prepare(r) \/ Decide(r)

TCSpec == TCInit /\ [][TCNext]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Invariants.                                                             *)
(***************************************************************************)
TCConsistent ==
  (*************************************************************************)
  (* No participant has committed while another has aborted.              *)
  (*************************************************************************)
  \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                       /\ rmState[r2] = "committed"

TCCommitPossible ==
  (*************************************************************************)
  (* If every participant is prepared, then each one is enabled to        *)
  (* commit (no deadlock preventing commit decisions).                     *)
  (*************************************************************************)
  (\A r \in RM : rmState[r] = "prepared") =>
      \A r \in RM : ENABLED (/\ rmState[r] = "prepared"
                             /\ canCommit
                             /\ rmState' = [rmState EXCEPT ![r] = "committed"])

-----------------------------------------------------------------------------
THEOREM TCSpec => [](TCTypeOK /\ TCConsistent /\ TCCommitPossible)
=============================================================================