---- MODULE CoverageStatisticsUnchanged ----
EXTENDS Naturals

\* This module exercises coverage statistics for different syntactic forms
\* of actions and UNCHANGED expressions (aliases, tuples, nested tuples).
\* It is not intended to model a realistic algorithm.

VARIABLES x, y

vars == <<x, y>>

\* Aliases for the state variables
a == x
b == y

\* Alias for a tuple of variables
ab == <<a, b>>

Init ==
    /\ x = 0
    /\ y = 0

\* Modifies x, leaves y unchanged (plain variable)
A1 ==
    /\ x' = x + 1
    /\ UNCHANGED y

\* Modifies y, leaves x unchanged via an alias
A2 ==
    /\ y' = y + 1
    /\ UNCHANGED a

\* Modifies x, leaves y unchanged via an alias
A3 ==
    /\ x' = x + 2
    /\ UNCHANGED b

\* Leaves everything unchanged via a tuple of variables
A4 ==
    UNCHANGED <<x, y>>

\* Leaves everything unchanged via the vars tuple
A5 ==
    UNCHANGED vars

\* Leaves everything unchanged via a tuple of aliases
A6 ==
    UNCHANGED <<a, b>>

\* Leaves everything unchanged via an alias for a tuple
A7 ==
    UNCHANGED ab

\* Leaves everything unchanged via nested tuples
A8 ==
    UNCHANGED <<<<x>>, <<y>>>>

\* Leaves everything unchanged via primed equalities
A9 ==
    /\ x' = x
    /\ y' = y

\* Modifies both variables via primed alias tuple
A10 ==
    /\ ab' = <<x + 1, y + 1>>

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

Spec == Init /\ [][Next]_vars

\* State constraint intended for model checking
Constraint == x < 20

\* Simple safety invariants
TypeOK ==
    /\ x \in Nat
    /\ y \in Nat

====