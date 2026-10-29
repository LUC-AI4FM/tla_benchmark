---- MODULE CoverageStatistics ----
EXTENDS Naturals

VARIABLES x, y

vars == <<x, y>>

\* Aliases for the state variables, used to test how coverage
\* reporting treats aliased variables inside UNCHANGED and tuples.
a == x
b == y
ab == <<a, b>>

Init ==
    /\ x = 0
    /\ y = 0

\* Modifies x, leaves y unchanged via plain variable.
A1 ==
    /\ x' = x + 1
    /\ UNCHANGED y

\* Modifies x, leaves y unchanged via alias.
A2 ==
    /\ x' = x + 2
    /\ UNCHANGED b

\* Modifies y, leaves x unchanged via tuple of a single variable.
A3 ==
    /\ y' = y + 1
    /\ UNCHANGED <<x>>

\* Modifies y, leaves x unchanged via tuple of an alias.
A4 ==
    /\ y' = 1 - y
    /\ UNCHANGED <<a>>

\* Leaves everything unchanged via the vars tuple.
A5 ==
    UNCHANGED vars

\* Leaves everything unchanged via a tuple of aliases.
A6 ==
    UNCHANGED ab

\* Leaves everything unchanged via an explicit tuple of variables.
A7 ==
    UNCHANGED <<x, y>>

\* Leaves everything unchanged via nested tuples mixing aliases and variables.
A8 ==
    UNCHANGED <<a, <<y>>>>

\* Modifies both variables at once.
A9 ==
    /\ x' = x + 1
    /\ y' = y

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

Spec == Init /\ [][Next]_vars

\* State constraint intended for model checking to bound the state space.
Constraint == x < 20

\* Simple type-correctness invariant.
TypeOK ==
    /\ x \in Nat
    /\ y \in Nat

====