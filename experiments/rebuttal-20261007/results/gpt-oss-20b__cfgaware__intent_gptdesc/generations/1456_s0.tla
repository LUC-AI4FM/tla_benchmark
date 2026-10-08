------------------------------ MODULE MutableSubset ------------------------------
EXTENDS SET, FiniteSets

CONSTANTS U

VARIABLE subset

Init == subset \subset U

Next == subset' ∈ SUBSET(U)

TypeOK == subset ∈ SUBSET(U)

Inv == TypeOK

Spec == Init /\ [][Next]_<<subset>>

FullSetReached == subset = U

ElementGained(e) == /\ e \notin subset
                    /\ e ∈ subset'

Add3Transition == ElementGained(3)
-----------------------------------------------------------------