------------------------------ MODULE Github790 ------------------------------
EXTENDS Naturals, TLC

VARIABLE a

Init == a = 0

Next == a' = a

vars == <<a>>

Spec == Init /\ [][Next]_vars

AlwaysTrue == <>TRUE => <>[]TRUE

THEOREM AlwaysTrueTheorem == Spec => AlwaysTrue
=============================================================================