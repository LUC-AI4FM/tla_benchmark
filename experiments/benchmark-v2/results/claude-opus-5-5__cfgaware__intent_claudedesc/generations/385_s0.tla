------------------------------ MODULE TheoremInstanceTest ------------------------------
EXTENDS Naturals

CONSTANT C

VARIABLE x

ASSUME C \in Nat /\ C > 0

---------------------------------- MODULE ThmBase ----------------------------------
EXTENDS Naturals
CONSTANT D

DefEq3 == D = 3
DefPos == D > 0

THEOREM T1 == D = 3
THEOREM T2 == (D > 0) /\ (D < 1000)
THEOREM T3 == DefPos /\ (D + 1 > D)
=====================================================================================