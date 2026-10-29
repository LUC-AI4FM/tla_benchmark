------------------------------- MODULE TCommit -------------------------------
(***************************************************************************)
(* Specification of the Two-Phase Commit protocol at the level of the      *)
(* resource managers (RMs). Each RM moves between the states "working",    *)
(* "prepared", "committed" and "aborted". There is no coordinator and no   *)
(* message passing, and faults are not modeled.                            *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT RM   \* The set of participating resource managers

VARIABLE rmState   \* rmState[r] is the state of resource manager r

vars == << rmState >>

(***************************************************************************)
(* Type-correctness invariant.                                             *)
(***************************************************************************)
TCTypeOK ==
  rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

(***************************************************************************)
(* Initial predicate: every RM starts in the "working" state.              *)
(***************************************************************************)
Init ==
  rmState = [r \in RM |-> "working"]

(***************************************************************************)
(* An RM may commit only if every RM is prepared or has committed.         *)
(***************************************************************************)
canCommit ==
  \A r \in RM : rmState[r] \in {"prepared", "committed"}

(***************************************************************************)
(* An RM may abort only if no RM has committed.                            *)
(***************************************************************************)
notCommitted ==
  \A r \in RM : rmState[r] # "committed"

(***************************************************************************)
(* Actions of a single RM r.                                               *)
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

(***************************************************************************)
(* Next-state relation: some RM either prepares or decides.               *)
(***************************************************************************)
Next ==
  \E r \in RM : Prepare(r) \/ Decide(r)

(***************************************************************************)
(* Complete specification of the protocol.                                 *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Consistency invariant: no two RMs reach conflicting decisions, that is, *)
(* one RM committed while another RM aborted.                              *)
(***************************************************************************)
TCConsistent ==
  \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                       /\ rmState[r2] = "committed"

(***************************************************************************)
(* The protocol satisfies type correctness and consistency.                *)
(***************************************************************************)
THEOREM Spec => [](TCTypeOK /\ TCConsistent)
=============================================================================