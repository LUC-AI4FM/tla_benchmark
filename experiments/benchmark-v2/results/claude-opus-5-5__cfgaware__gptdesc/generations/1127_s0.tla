------------------------------ MODULE TCommit ------------------------------
CONSTANT RM       \* The set of participating resource managers

VARIABLE rmState  \* rmState[rm] is the state of resource manager rm.
-----------------------------------------------------------------------------
TCTypeOK ==
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

TCInit ==   rmState = [rm \in RM |-> "working"]
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)

canCommit == \A rm \in RM : rmState[rm] \in {"prepared", "committed"}
  (*************************************************************************)
  (* True iff all RMs are in the "prepared" or "committed" state.          *)
  (*************************************************************************)

notCommitted == \A rm \in RM : rmState[rm] # "committed"
  (*************************************************************************)
  (* True iff no resource manager has decided to commit.                   *)
  (*************************************************************************)
-----------------------------------------------------------------------------
Prepare(rm) == /\ rmState[rm] = "working"
               /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]

Decide(rm)  == \/ /\ rmState[rm] = "prepared"
                  /\ canCommit
                  /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
               \/ /\ rmState[rm] \in {"working", "prepared"}
                  /\ notCommitted
                  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]

TCNext == \E rm \in RM : Prepare(rm) \/ Decide(rm)
  (*************************************************************************)
  (* The next-state action.                                                *)
  (*************************************************************************)
-----------------------------------------------------------------------------
TCConsistent ==
  (*************************************************************************)
  (* A state predicate asserting that two RMs have not arrived at          *)
  (* conflicting decisions.                                                *)
  (*************************************************************************)
  \A rm1, rm2 \in RM : ~ /\ rmState[rm1] = "aborted"
                         /\ rmState[rm2] = "committed"
-----------------------------------------------------------------------------
TCSpec == TCInit /\ [][TCNext]_rmState
  (*************************************************************************)
  (* The complete specification of the protocol.                           *)
  (*************************************************************************)
-----------------------------------------------------------------------------
THEOREM TCSpec => [](TCTypeOK /\ TCConsistent)
=============================================================================