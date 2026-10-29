---------------------------- MODULE APBarrier -------------------------------
(***************************************************************************)
(* Wrapper around the Barrier specification that adds Apalache type       *)
(* annotations. The Barrier module itself is unchanged.                    *)
(*                                                                         *)
(* This module has no transition relation, temporal specification or      *)
(* proof obligations of its own. Init, Next, Spec and all invariants and   *)
(* properties come from the instantiated Barrier module.                   *)
(***************************************************************************)
EXTENDS Integers

CONSTANTS
    \* @type: Int;
    N

VARIABLES
    \* @type: Int -> Str;
    pc

\* Apalache can't infer the type of vars because it is a 1-tuple, so the
\* tuple of variables is redefined here to disambiguate its type.
vars == << pc >>

INSTANCE Barrier
=============================================================================