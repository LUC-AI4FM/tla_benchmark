---------------------------- MODULE MC_TCommit ----------------------------
(***************************************************************************)
(* Thin wrapper around TCommit adding Apalache type annotations and a     *)
(* concrete value for the set of resource managers.  The commit protocol  *)
(* and its properties come from the instantiated TCommit module.          *)
(***************************************************************************)

CONSTANT
    \* @type: Set(Str);
    RM

VARIABLE
    \* @type: Str -> Str;
    rmState

INSTANCE TCommit

\* Concrete set of resource managers for model checking (e.g. RM <- RMVal)
RMVal == {"r1", "r2", "r3"}

\* Convenience aliases for the inherited protocol definitions
Init == TCInit

Next == TCNext

Spec == TCSpec

\* Inherited safety invariants
TypeOK == TCTypeOK

Consistent == TCConsistent

=============================================================================