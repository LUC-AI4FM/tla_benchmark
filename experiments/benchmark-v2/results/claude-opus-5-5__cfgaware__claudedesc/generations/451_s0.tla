---------------------------- MODULE test61 ----------------------------
(***************************************************************************)
(* Test of parameterized instantiation.  The module test61a is            *)
(* instantiated in two equivalent ways: once via a parameterized          *)
(* instance operator IM(x), and once via an explicit substitution         *)
(* x <- y.  Both ISpec and JSpec should denote the same specification.    *)
(***************************************************************************)
EXTENDS Naturals

VARIABLE y

IM(x) == INSTANCE test61a

ISpec == IM(y)!Spec

JM == INSTANCE test61a WITH x <- y

JSpec == JM!Spec

Invariant == y \in 0..4

=============================================================================