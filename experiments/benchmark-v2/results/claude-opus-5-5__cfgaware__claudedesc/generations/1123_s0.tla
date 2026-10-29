---------------------------- MODULE APATCommit ----------------------------
(***************************************************************************)
(* Apalache-compatible wrapper around the TCommit specification of the     *)
(* transaction commit protocol. The TCommit definitions are inlined here   *)
(* so that the module is self-contained, and type annotations are given    *)
(* for Apalache.                                                           *)
(***************************************************************************)

CONSTANT
    \* @type: Set(Str);
    RM          \* The set of participating resource managers

\* Concrete value for RM used in model checking
RMVal == {"r1", "r2", "r3"}

VARIABLE
    \* @type: Str -> Str;
    rmState     \* rmState[r] is the state of resource manager r

-----------------------------------------------------------------------------
(* Inherited behavior of TCommit *)

TCTypeOK ==
    rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

TCInit == rmState = [r \in RM |-> "working"]

canCommit == \A r \in RM : rmState[r] \in {"prepared", "committed"}

notCommitted == \A r \in RM : rmState[r] # "committed"

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

TCSpec == TCInit /\ [][TCNext]_rmState

TCConsistent ==
    \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                         /\ rmState[r2] = "committed"

THEOREM TCSpec => [](TCTypeOK /\ TCConsistent)
=============================================================================