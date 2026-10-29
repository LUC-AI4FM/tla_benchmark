---------------------------- MODULE APABarrier ----------------------------
(***************************************************************************)
(* A lightweight wrapper around the Barrier specification. It provides     *)
(* Apalache type annotations for the constant N and the variable pc, and   *)
(* locally redefines the tuple vars to settle the type of the 1-tuple      *)
(* used by the instantiated specification. The Barrier module itself is    *)
(* left unchanged.                                                         *)
(***************************************************************************)
EXTENDS Integers

CONSTANT
    \* @type: Int;
    N

VARIABLE
    \* @type: Int -> Str;
    pc

\* Local redefinition to disambiguate the type of the 1-tuple.
\* @type: <<Int -> Str>>;
vars == << pc >>

B == INSTANCE Barrier WITH N <- N, pc <- pc

Init == B!Init

Next == B!Next

Spec == Init /\ [][Next]_vars

=============================================================================