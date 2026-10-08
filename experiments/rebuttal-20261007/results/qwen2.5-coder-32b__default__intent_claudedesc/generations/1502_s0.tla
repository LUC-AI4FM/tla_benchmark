------------------------------- MODULE HigherOrderOperatorDemo -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS 
    \* A higher-order constant that takes a natural number and returns a set of natural numbers
    NextValuesOp

VARIABLES x

Init == x = 0

Next ==
    /\ \/ x' \in NextValuesOp(x)
       \/ x' \in {S \subseteq {1, 2, 3} : Cardinality(S) <= 2}

Spec ==
    /\ Init
    /\ [][Next]_<<x>>

=============================================================================