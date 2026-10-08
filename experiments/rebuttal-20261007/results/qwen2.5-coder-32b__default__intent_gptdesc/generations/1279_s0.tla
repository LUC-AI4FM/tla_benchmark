------------------------------- MODULE SimpleSystem -------------------------------
EXTENDS Integers

CONSTANTS AllowedValues

VARIABLES x

Init == x = 0

Next ==
    \/ /\ x' \in AllowedValues
       /\ x' > 0
    \/ x' = x

Spec ==
    /\ Init
    /\ [][Next]_<<x>>

Inv ==
    x /= 0

TransConstraint ==
    [](x' = x \/ (x' \in AllowedValues /\ x' > 0))

TypeOK ==
    /\ x \in Integers
    /\ AllowedValues \subseteq Integers

SpecWithProps ==
    /\ Spec
    /\ TypeOK
    /\ Inv
    /\ TransConstraint

=============================================================================