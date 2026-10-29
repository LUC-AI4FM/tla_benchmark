------------------------------ MODULE test55 ------------------------------
EXTENDS Naturals

VARIABLE z

vars == <<z>>

Init == z = 0

Next == z' = 1 - z

I == INSTANCE test55a WITH x <- z, y <- z

Spec == Init /\ [][Next]_z /\ WF_z(Next)

TypeOK == z \in {0, 1}

InstanceInit == I!Init

InstanceF == I!F

InstanceG == I!G

Invariant == TypeOK /\ I!F /\ I!G

SafeProp == I!SafeSpec

LiveProp == I!LiveSpec

Liveness == []<>(z = 1) /\ []<>(z = 0)

THEOREM Spec => []Invariant
THEOREM Spec => SafeProp
THEOREM Spec => LiveProp
THEOREM Spec => Liveness
=============================================================================