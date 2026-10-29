---- MODULE CoverageStatistics ----
EXTENDS Naturals

VARIABLES x, y

vars == <<x, y>>

\* Aliases for the state variables, used to test how coverage
\* reporting treats aliased variables in UNCHANGED expressions.
a == x
b == y

\* Tuple aliases.
ab == <<a, b>>
yy == <<y>>

Init ==
    /\ x = 0
    /\ y = 0

\* Modifies x, leaves y unchanged (plain variable).
A ==
    /\ x' = x + 1
    /\ UNCHANGED y

\* Modifies y, leaves x unchanged via an alias.
B ==
    /\ y' = y + 1
    /\ UNCHANGED a

\* Modifies x, leaves y unchanged via a single-element tuple alias.
C ==
    /\ x' = x + 2
    /\ UNCHANGED yy

\* Leaves everything unchanged via the vars tuple.
D ==
    UNCHANGED vars

\* Leaves everything unchanged via a tuple of aliases.
E ==
    UNCHANGED ab

\* Leaves everything unchanged via an explicit tuple of variables.
F ==
    UNCHANGED <<x, y>>

\* Leaves everything unchanged via a tuple of aliases written inline.
G ==
    UNCHANGED <<a, b>>

\* Modifies both variables.
H ==
    /\ x' = x + 1
    /\ y' = y + 1

\* Leaves variables unchanged via nested tuple.
I ==
    UNCHANGED <<x, <<y>>>>

\* Modifies y, leaves x unchanged via explicit primed equality.
J ==
    /\ x' = x
    /\ y' = y + 2

Next ==
    \/ A
    \/ B
    \/ C
    \/ D
    \/ E
    \/ F
    \/ G
    \/ H
    \/ I
    \/ J

Spec == Init /\ [][Next]_vars

\* State constraint intended for model checking.
Constraint == x < 20

TypeOK ==
    /\ x \in Nat
    /\ y \in Nat

====