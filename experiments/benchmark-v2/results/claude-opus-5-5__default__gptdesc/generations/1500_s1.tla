---------------------------- MODULE CoverageStatistics ----------------------------
(***************************************************************************)
(* A small specification used to exercise coverage statistics for         *)
(* different syntactic forms of actions and UNCHANGED expressions.        *)
(* The purpose is to test how coverage reporting treats aliases, tuples,  *)
(* and UNCHANGED forms rather than to model a realistic algorithm.        *)
(***************************************************************************)
EXTENDS Naturals

VARIABLES x, y

vars == <<x, y>>

\* Aliases for the state variables
a == x
b == y

\* Alias for the tuple of variables
ab == <<a, b>>

Init ==
    /\ x = 0
    /\ y = 0

\* Modify x, leave y unchanged via plain variable
A1 ==
    /\ x' = x + 1
    /\ UNCHANGED y

\* Modify x, leave y unchanged via alias
A2 ==
    /\ x' = x + 1
    /\ UNCHANGED b

\* Modify y, leave x unchanged via tuple
A3 ==
    /\ y' = y + 1
    /\ UNCHANGED <<x>>

\* Modify y, leave x unchanged via tuple of alias
A4 ==
    /\ y' = y + 1
    /\ UNCHANGED <<a>>

\* Leave all variables unchanged via the vars tuple
A5 == UNCHANGED vars

\* Leave all variables unchanged via the alias tuple
A6 == UNCHANGED ab

\* Leave all variables unchanged via an explicit tuple
A7 == UNCHANGED <<x, y>>

\* Leave all variables unchanged via nested tuples of aliases
A8 == UNCHANGED <<<<a>>, <<b>>>>

\* Leave all variables unchanged via conjunction of UNCHANGED forms
A9 ==
    /\ UNCHANGED x
    /\ UNCHANGED b

\* Explicit primed equalities leaving variables unchanged
A10 ==
    /\ x' = x
    /\ y' = y

\* Modify both variables at once
A11 ==
    /\ x' = x + 1
    /\ y' = y + 1

Next ==
    \/ A1
    \/ A2
    \/ A3
    \/ A4
    \/ A5
    \/ A6
    \/ A7
    \/ A8
    \/ A9
    \/ A10
    \/ A11

Spec == Init /\ [][Next]_vars

\* State constraint for model checking
Constraint == x < 20

\* Type invariant
TypeOK ==
    /\ x \in Nat
    /\ y \in Nat
=============================================================================