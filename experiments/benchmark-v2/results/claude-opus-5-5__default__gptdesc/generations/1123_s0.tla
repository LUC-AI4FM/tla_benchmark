------------------------------ MODULE APATCommit ------------------------------
(***************************************************************************)
(* A thin wrapper around the TCommit specification (Transaction Commit).   *)
(* It adds Apalache type annotations to the constant RM and the variable   *)
(* rmState. It then instantiates TCommit with no explicit substitutions,   *)
(* so RM and rmState are bound implicitly to the identically named         *)
(* constant and variable declared here.                                    *)
(*                                                                         *)
(* The commit protocol logic is inherited from TCommit, including          *)
(* TCTypeOK, TCInit, TCNext, TCConsistent and TCSpec.                      *)
(***************************************************************************)

CONSTANT
    \* The set of resource managers
    \* @type: Set(Str);
    RM

VARIABLE
    \* The state of each resource manager:
    \* "working", "prepared", "committed" or "aborted"
    \* @type: Str -> Str;
    rmState

INSTANCE TCommit

(***************************************************************************)
(* A concrete value for the set of resource managers, for model checking  *)
(* (for example, with Apalache: --cinit or ConstInit-style binding).      *)
(***************************************************************************)
RMVal == { "r1", "r2", "r3" }

(***************************************************************************)
(* Aliases to the inherited protocol definitions.                          *)
(***************************************************************************)
Init == TCInit

Next == TCNext

Spec == TCSpec

(***************************************************************************)
(* Inherited safety invariants.                                            *)
(***************************************************************************)
TypeOK == TCTypeOK

Consistent == TCConsistent

THEOREM Spec => [](TypeOK /\ Consistent)
===============================================================================