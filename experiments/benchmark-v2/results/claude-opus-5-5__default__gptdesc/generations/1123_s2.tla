---- MODULE MC_TCommit ----
(***************************************************************************)
(* A thin wrapper around the TCommit specification that adds Apalache     *)
(* type annotations and a concrete value for the resource manager set.    *)
(* The commit protocol logic and properties come from TCommit.            *)
(***************************************************************************)

CONSTANT
    \* @type: Set(Str);
    RM

VARIABLE
    \* @type: Str -> Str;
    rmState

INSTANCE TCommit

\* A concrete set of resource managers, for use with ConstInit / cfg files.
\* @type: Set(Str);
RMVal == { "r1", "r2", "r3" }

\* Apalache-style constant initialization.
ConstInit == RM = RMVal

\* Behavior inherited from the instantiated TCommit module.
Init == TCInit

Next == TCNext

Spec == Init /\ [][Next]_rmState

\* Safety invariants inherited from TCommit.
TypeOK == TCTypeOK

Consistent == TCConsistent

THEOREM Spec => [](TypeOK /\ Consistent)
====