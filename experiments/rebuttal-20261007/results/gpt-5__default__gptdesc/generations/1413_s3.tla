----------------------------- MODULE Github790 -----------------------------
EXTENDS Naturals

CONSTANTS DummyConst

VARIABLES a

Init == a = 0

Next == a' = a

Spec == Init /\ [][Next]_a

AlwaysTrue == <>TRUE => <>[]TRUE
============================================================================