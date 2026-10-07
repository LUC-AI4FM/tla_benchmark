----------------------------- MODULE B -----------------------------
EXTENDS TLC

VARIABLES x

Switch(old, new) == new = ~old

A == Switch(x, x')
B == Switch(x, x')

Init == x = FALSE

Next == A \/ B

Spec == Init /\ [] (Next)
====================================================================