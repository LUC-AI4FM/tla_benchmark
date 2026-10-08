------------------------------- MODULE InitializationPattern -------------------------------
EXTENDS Integers, TLC

CONSTANTS Init

VARIABLES s

Init == \E val \in 0..1 : s = val /\ s < 1

Next == UNCHANGED s

Spec == /\ Init
        /\ []Next
        /\ []Inv

Inv == s < 1
================================================================================