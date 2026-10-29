---------------------------- MODULE TCommit ----------------------------
(***************************************************************************)
(* A simple single-phase atomic commit protocol for a fixed set of        *)
(* resource managers (RMs). Each RM starts out "working". It may prepare  *)
(* or abort at any time before a final decision is reached. A prepared RM *)
(* may commit only once every RM has reached at least the prepared state. *)
(*                                                                         *)
(* Model checking: instantiate RM with three concrete values, e.g.         *)
(*   RM <- {"r1", "r2", "r3"}                                              *)
(* and check the invariants TCTypeOK and TCConsistent. Deadlock checking   *)
(* need not be enabled, and there is no liveness requirement.             *)
(***************************************************************************)
EXTENDS FiniteSets

CONSTANT RM          \* The set of participating resource managers

ASSUME Cardinality(RM) = 3

VARIABLE rmState     \* rmState[r] is the state of resource manager r

vars == << rmState >>

States == {"working", "prepared", "committed", "aborted"}

-----------------------------------------------------------------------------
(* Type correctness invariant *)
TCTypeOK == rmState \in [RM -> States]

TCInit == rmState = [r \in RM |-> "working"]

(* All RMs have reached at least the prepared state. *)
canCommit == \A r \in RM : rmState[r] \in {"prepared", "committed"}

(* No RM has committed, so aborting is still allowed. *)
notCommitted == \A r \in RM : rmState[r] # "committed"

-----------------------------------------------------------------------------
(* A working RM signals readiness to commit. *)
Prepare(r) ==
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

(* A prepared RM commits once all RMs are at least prepared. *)
Commit(r) ==
    /\ rmState[r] = "prepared"
    /\ canCommit
    /\ rmState' = [rmState EXCEPT ![r] = "committed"]

(* An RM aborts before a final (commit) decision has been reached. *)
Abort(r) ==
    /\ rmState[r] \in {"working", "prepared"}
    /\ notCommitted
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

Decide(r) == Commit(r) \/ Abort(r)

TCNext == \E r \in RM : Prepare(r) \/ Decide(r)

TCSpec == TCInit /\ [][TCNext]_vars

-----------------------------------------------------------------------------
(* Consistency invariant: no two RMs reach conflicting decisions. *)
TCConsistent ==
    \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                         /\ rmState[r2] = "committed"

THEOREM TCSpec => [](TCTypeOK /\ TCConsistent)
=============================================================================