------------------------------- MODULE TCommit -------------------------------
(***************************************************************************)
(* Two-Phase Commit modeled abstractly from the point of view of the      *)
(* resource managers (RMs).  Each RM moves through the states "working",   *)
(* "prepared", "committed" and "aborted".  No coordinator, no messages,    *)
(* and no failures beyond the abort/commit logic are modeled.             *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT RM          \* The set of participating resource managers

VARIABLE rmState     \* rmState[r] is the state of resource manager r

vars == << rmState >>

-----------------------------------------------------------------------------
States == {"working", "prepared", "committed", "aborted"}

(***************************************************************************)
(* Type-correctness invariant.                                             *)
(***************************************************************************)
TypeOK == rmState \in [RM -> States]

(***************************************************************************)
(* Initial predicate: every RM starts in the "working" state.             *)
(***************************************************************************)
Init == rmState = [r \in RM |-> "working"]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Auxiliary predicates.                                                   *)
(***************************************************************************)

(* An RM may commit only if every RM is prepared or has already committed. *)
canCommit == \A r \in RM : rmState[r] \in {"prepared", "committed"}

(* An RM may abort only if no RM has committed. *)
notCommitted == \A r \in RM : rmState[r] # "committed"

-----------------------------------------------------------------------------
(***************************************************************************)
(* Actions of an individual RM.                                            *)
(***************************************************************************)

(* A working RM may prepare. *)
Prepare(r) ==
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

(* An RM decides to commit or to abort. *)
Decide(r) ==
    \/ /\ rmState[r] = "prepared"
       /\ canCommit
       /\ rmState' = [rmState EXCEPT ![r] = "committed"]
    \/ /\ rmState[r] \in {"working", "prepared"}
       /\ notCommitted
       /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Next-state relation: some RM performs either Prepare or Decide.         *)
(***************************************************************************)
Next == \E r \in RM : Prepare(r) \/ Decide(r)

(***************************************************************************)
(* The complete specification (no fairness conditions are assumed).        *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Consistency invariant: no two RMs reach conflicting decisions, i.e.,    *)
(* it is never the case that one RM has committed and another aborted.     *)
(***************************************************************************)
Consistent ==
    \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                         /\ rmState[r2] = "committed"

-----------------------------------------------------------------------------
(***************************************************************************)
(* The invariants asserted as properties of the protocol.                  *)
(***************************************************************************)
THEOREM Spec => [](TypeOK /\ Consistent)

=============================================================================