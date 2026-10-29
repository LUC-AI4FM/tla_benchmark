--------------------------- MODULE test55 ---------------------------
EXTENDS Naturals

VARIABLE z

I == INSTANCE test55a WITH x <- z, y <- z

Init == z = 0

Next == z' = 1 - z

Spec == Init /\ [][Next]_z /\ WF_z(Next)

TypeOK == z \in {0, 1}

InstInv == I!F /\ I!G

Invariant == TypeOK /\ InstInv

InstInit == I!Init

SafeProp == I!SafeSpec

LiveProp == I!LiveSpec

THEOREM Spec => []Invariant
THEOREM Spec => SafeProp
THEOREM Spec => LiveProp
=====================================================================