--------------------------- MODULE test55 ---------------------------
EXTENDS Naturals

VARIABLE z

vars == <<z>>

I == INSTANCE test55a WITH x <- z, y <- z

Init == z = 0

Next == z' = 1 - z

Spec == Init /\ [][Next]_z /\ WF_z(Next)

TypeOK == z \in {0, 1}

InstanceInit == I!Init

Invariant == I!F /\ I!G

SafeProperty == I!SafeSpec

LiveProperty == I!LiveSpec

THEOREM Spec => []TypeOK
THEOREM Spec => []Invariant
THEOREM Spec => SafeProperty
THEOREM Spec => LiveProperty
=============================================================================