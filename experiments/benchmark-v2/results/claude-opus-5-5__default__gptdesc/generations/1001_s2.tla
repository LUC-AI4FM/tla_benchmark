---------------------------- MODULE ApaBarrier ----------------------------
(***************************************************************************)
(* A lightweight wrapper around the module Barrier.  Its purpose is to     *)
(* attach Apalache type annotations to the constant N and the variable pc  *)
(* while leaving the original Barrier module unchanged.                    *)
(*                                                                         *)
(* The tuple vars is redefined locally as << pc >> so that Apalache can    *)
(* resolve the type of the 1-tuple used by the instantiated specification. *)
(* Apalache cannot infer the type of a 1-tuple without this annotation.    *)
(*                                                                         *)
(* This module adds no transition relation, temporal specification or      *)
(* proof obligations of its own.  Init, Next and Spec only refer to the    *)
(* definitions of the instantiated Barrier module.                         *)
(***************************************************************************)

CONSTANT
    \* @type: Int;
    N

VARIABLE
    \* @type: Int -> Str;
    pc

\* Apalache cannot infer the type of a 1-tuple, so the type is given explicitly.
\* @type: <<Int -> Str>>;
vars == << pc >>

\* The original Barrier specification, instantiated with the same N and pc.
B == INSTANCE Barrier WITH N <- N, pc <- pc

\* Initial state, transition relation and temporal specification are taken
\* unchanged from Barrier.
Init == B!Init

Next == B!Next

Spec == B!Spec

=============================================================================