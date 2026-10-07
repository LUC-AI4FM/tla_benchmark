---- MODULE TrivialOneVar ----
EXTENDS Naturals

CONSTANTS Dummy

VARIABLES x

Vars == << x >>

Init == x = 0

Next == UNCHANGED x

Spec == Init /\ [] [Next]_Vars
====