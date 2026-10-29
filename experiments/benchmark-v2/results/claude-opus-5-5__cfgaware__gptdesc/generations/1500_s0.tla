---- MODULE CoverageStatistics ----
EXTENDS Naturals

VARIABLES x, y

vars == <<x, y>>

\* Aliases for the variables, used to test coverage reporting.
a == x
b == y
ab == <<a, b>>

Init ==
    /\ x = 0
    /\ y = 0

\* Modifies x, leaves y unchanged via a plain variable.
A ==
    /\ x' = x + 1
    /\ UNCHANGED y

\* Modifies y, leaves x unchanged via an alias.
B ==
    /\ y' = y + 1
    /\ UNCHANGED a

\* Modifies x, leaves y unchanged via a one-element tuple.
C ==
    /\ x' = x + 2
    /\ UNCHANGED <<y>>

\* Stutters, leaving both unchanged via the vars tuple.
D ==
    /\ UNCHANGED vars

\* Stutters, leaving both unchanged via a tuple of aliases.
E ==
    /\ UNCHANGED <<a, b>>

\* Stutters, leaving both unchanged via the alias tuple.
F ==
    /\ UNCHANGED ab

\* Modifies y, leaves x unchanged via a nested tuple.
G ==
    /\ y' = y + 2
    /\ UNCHANGED <<<<x>>>>

\* Modifies both variables.
H ==
    /\ x' = x + 1
    /\ y' = y + 1

Next ==
    \/ A
    \/ B
    \/ C
    \/ D
    \/ E
    \/ F
    \/ G
    \/ H

Spec == Init /\ [][Next]_vars

Constraint == x < 20 /\ y < 20

====