------------------------------ MODULE MC_TCommit ------------------------------
(***************************************************************************)
(* A thin wrapper around TCommit that adds Apalache type annotations and   *)
(* a concrete value for the set of resource managers.                      *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    \* The set of participating resource managers
    \* @type: Set(Str);
    RM

VARIABLES
    \* rmState[r] is the state of resource manager r
    \* @type: Str -> Str;
    rmState

\* Instantiate TCommit without explicit substitutions:
\* RM and rmState are substituted implicitly by name.
INSTANCE TCommit

\* Concrete set of resource managers used for model checking
\* @type: Set(Str);
RMVal == { "r1", "r2", "r3" }

\* Behavior and properties are inherited from the instantiated module.
Init == TCInit

Next == TCNext

Spec == TCSpec

\* Inherited safety invariants
TypeOK == TCTypeOK

Consistent == TCConsistent

================================================================================