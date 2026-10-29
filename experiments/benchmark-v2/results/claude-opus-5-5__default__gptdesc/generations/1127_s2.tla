------------------------------ MODULE TCommit ------------------------------
(***************************************************************************)
(* Two-Phase Commit protocol at the level of resource managers (RMs).      *)
(* Each RM moves through the states working, prepared, committed and       *)
(* aborted. No coordinator, messages or failures are modeled.              *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT RM          \* The set of participating resource managers

VARIABLE rmState     \* rmState[r] is the state of resource manager r

vars == << rmState >>

-----------------------------------------------------------------------------
States == {"working", "prepared", "committed", "aborted"}

TCTypeOK ==
    rmState \in [RM -> States]

TCInit ==
    rmState = [r \in RM |-> "working"]

(***************************************************************************)
(* An RM may commit only if every RM is prepared or already committed.     *)
(***************************************************************************)
canCommit ==
    \A r \in RM : rmState[r] \in {"prepared", "committed"}

(***************************************************************************)
(* An RM may abort only if no RM has committed.                            *)
(***************************************************************************)
notCommitted ==
    \A r \in RM : rmState[r] # "committed"

-----------------------------------------------------------------------------
(***************************************************************************)
(* Actions                                                                 *)
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

TCNext ==
    \E r \in RM : Prepare(r) \/ Decide(r)

Init == TCInit
Next == TCNext

Spec == TCInit /\ [][TCNext]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

\* No two RMs reach conflicting decisions.
TCConsistent ==
    \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                         /\ rmState[r2] = "committed"

TypeInvariant == TCTypeOK
Consistency   == TCConsistent

THEOREM Spec => [](TCTypeOK /\ TCConsistent)
=============================================================================