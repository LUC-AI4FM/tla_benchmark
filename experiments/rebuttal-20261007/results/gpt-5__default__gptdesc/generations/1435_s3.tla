----------------------------- MODULE TrivialOneVar -----------------------------

EXTENDS Integers

CONSTANTS UnusedConst

VARIABLES x

Init == x = 0

Next == x' = x

Spec == Init /\ [] (Next)

===============================================================================