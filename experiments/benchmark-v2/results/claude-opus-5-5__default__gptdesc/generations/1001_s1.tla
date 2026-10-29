------------------------------- MODULE APABarrier -------------------------------
(***************************************************************************)
(* Lightweight wrapper around the Barrier specification whose sole purpose *)
(* is to attach Apalache type annotations to the constant and variable of  *)
(* Barrier without modifying the original module.                          *)
(***************************************************************************)
EXTENDS Integers

CONSTANT
    \* @type: Int;
    N

VARIABLE
    \* @type: Int -> Str;
    pc

\* Redefine vars locally to disambiguate the type of the 1-tuple
\* used by the instantiated specification.
\* @type: <<Int -> Str>>;
vars == << pc >>

\* Instantiate the original Barrier module; N and pc are substituted
\* implicitly by the identically named constant and variable above.
B == INSTANCE Barrier

\* Re-export the behavior of the instantiated Barrier specification.
Init == B!Init

Next == B!Next

Spec == B!Spec

=============================================================================