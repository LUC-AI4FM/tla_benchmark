------------------------------- MODULE InitializationPattern -------------------------------

EXTENDS Naturals, TLC, Integers

CONSTANTS Init

VARIABLES s

Init == \E val \in 0..1 : s = val /\ s < 1

Next == UNCHANGED s

Spec ==
    \/ <<Init(s), []Next>>_<<s>>
    \/ [](Inv)

Inv == s < 1

================================================================================