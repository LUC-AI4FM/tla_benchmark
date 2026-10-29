---------------------------- MODULE MCTCommit ----------------------------
(***************************************************************************)
(* Model-checking companion for the transaction commit specification.      *)
(* The TCommit definitions are inlined here so that the module parses on   *)
(* its own; the companion part adds two state predicates over rmState:     *)
(* a type-correctness condition and a consistency condition.               *)
(***************************************************************************)

CONSTANT RM       \* The set of participating resource managers

VARIABLE rmState  \* rmState[r] is the state of resource manager r.

-----------------------------------------------------------------------------
(*************************** TCommit definitions ***************************)

TCInit == rmState = [r \in RM |-> "working"]

canCommit == \A r \in RM : rmState[r] \in {"prepared", "committed"}

notCommitted == \A r \in RM : rmState[r] # "committed"

Prepare(r) == /\ rmState[r] = "working"
              /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

Decide(r) == \/ /\ rmState[r] = "prepared"
                /\ canCommit
                /\ rmState' = [rmState EXCEPT ![r] = "committed"]
             \/ /\ rmState[r] \in {"working", "prepared"}
                /\ notCommitted
                /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

TCNext == \E r \in RM : Prepare(r) \/ Decide(r)

TCSpec == TCInit /\ [][TCNext]_rmState

-----------------------------------------------------------------------------
(************************ Companion state predicates ***********************)

TCTypeOK ==
  rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

TCConsistent ==
  \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                       /\ rmState[r2] = "committed"

=============================================================================