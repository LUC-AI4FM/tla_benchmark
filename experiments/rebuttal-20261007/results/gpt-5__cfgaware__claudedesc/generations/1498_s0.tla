---- MODULE B ----
VARIABLES x

Init == x = FALSE

Switch == x' = ~x

A == Switch
B == Switch

Next == A \/ B
====