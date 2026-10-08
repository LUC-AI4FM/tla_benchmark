------------------------------- MODULE InitializationPattern -------------------------------

EXTENDS Integers, TLC, SpecifyingSystemBehavior

CONSTANTS Init

VARIABLES s

Init == /\ s = 0

Next == UNCHANGED s

Spec == 
    /\ Init
    /\ [][Next]_<<s>>
    /\ Inv

Inv == s < 1

================================================================================