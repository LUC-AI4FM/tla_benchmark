---- MODULE TrivialStutter ----
EXTENDS Integers

CONSTANTS Dummy

VARIABLES x

Init == x = 0

Next == x' = x

Spec == Init /\ []Next
====