------------------------------ MODULE MC3_TCommit ------------------------------
(***************************************************************************)
(* Apalache-compatible wrapper around the TCommit specification.           *)
(* The TCommit definitions are inlined so that this module is              *)
(* self-contained and passes SANY on its own.                              *)
(***************************************************************************)

CONSTANTS
    \* @type: Set(Str);
    RM

VARIABLES
    \* @type: Str -> Str;
    rmState

\* Concrete instantiation of the resource managers for model checking
ConstInit == RM = {"r1", "r2", "r3"}

vars == << rmState >>

-----------------------------------------------------------------------------
(* TCommit *)

TCTypeOK ==
    rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

TCInit ==
    rmState = [r \in RM |-> "working"]

canCommit ==
    \A r \in RM : rmState[r] \in {"prepared", "committed"}

notCommitted ==
    \A r \in RM : rmState[r] # "committed"

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

TCSpec ==
    TCInit /\ [][TCNext]_vars

TCConsistent ==
    \A r1, r2 \in RM :
        ~ /\ rmState[r1] = "aborted"
          /\ rmState[r2] = "committed"

-----------------------------------------------------------------------------
(* Wrapper definitions used by the model-checking configuration.           *)
(* SPECIFICATION TCSpec                                                    *)
(* INVARIANTS TCTypeOK TCConsistent                                        *)
(* CHECK_DEADLOCK FALSE                                                    *)

Init == TCInit

Next == TCNext

Spec == TCSpec

THEOREM Spec => [](TCTypeOK /\ TCConsistent)

=============================================================================