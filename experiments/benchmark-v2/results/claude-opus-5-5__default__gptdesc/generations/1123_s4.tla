---------------------------- MODULE APATCommit ----------------------------
(***************************************************************************)
(* Thin wrapper around the TCommit specification that adds Apalache type   *)
(* annotations and a concrete value for the set of resource managers.     *)
(* The commit protocol logic and its properties come from TCommit.         *)
(***************************************************************************)

CONSTANTS
    \* @type: Set(Str);
    RM

VARIABLES
    \* @type: Str -> Str;
    rmState

INSTANCE TCommit

(***************************************************************************)
(* Concrete set of resource managers, used to instantiate RM.              *)
(***************************************************************************)
RMVal == {"r1", "r2", "r3"}

(***************************************************************************)
(* Local aliases for the inherited protocol definitions.                   *)
(***************************************************************************)
Init == TCInit

Next == TCNext

Spec == TCSpec

(***************************************************************************)
(* Safety invariants inherited from TCommit.                               *)
(***************************************************************************)
TypeOK == TCTypeOK

Consistent == TCConsistent

=============================================================================