---------------------------- MODULE PrimedFilter ----------------------------
EXTENDS Integers

VARIABLE x

vars == <<x>>

Domain == 0..1

Empty == <<>>

TypeOK == x \in {Empty} \cup Domain

Init == x = Empty

\* Forward-looking constraint: the next value is chosen from the domain
\* and the transition is only permitted if the primed value is strictly positive.
Step == \E v \in Domain : /\ x' = v
                          /\ x' > 0

Next == Step

Spec == Init /\ [][Next]_vars

\* Safety: type invariant
Inv == TypeOK

\* Safety: any value ever reached after initialization is strictly positive
PositiveAfterInit == x # Empty => x = 1

\* Action property: every non-stuttering step lands on a positive domain value
StepsPositive == [][x' \in Domain /\ x' > 0]_vars

THEOREM Spec => [](TypeOK /\ PositiveAfterInit)
=============================================================================