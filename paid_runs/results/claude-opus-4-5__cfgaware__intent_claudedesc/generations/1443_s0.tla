---------------------------- MODULE spec ----------------------------

VARIABLE counter

Init == counter = 0

Next == counter' = (counter + 1) % 3

Spec == Init /\ [][Next]_counter /\ WF_counter(Next)

\* Predicate that holds when counter reaches 2
ReachesTwo == counter = 2

\* Predicate that holds when counter equals 1
EqualsOne == counter = 1

\* Predicate that captures the wrap-around transition from 2 back to 0
WrapAround == counter = 2 /\ counter' = 0

\* _POSSIBLE directives for TLC to track whether predicates are satisfied
ReachesTwo_POSSIBLE == ReachesTwo
EqualsOne_POSSIBLE == EqualsOne
WrapAround_POSSIBLE == WrapAround

\* Postcondition asserting TLC recorded exactly one witness for each predicate
Postcondition ==
    /\ TLCGet("spec")[ReachesTwo_POSSIBLE] = 1
    /\ TLCGet("spec")[EqualsOne_POSSIBLE] = 1
    /\ TLCGet("spec")[WrapAround_POSSIBLE] = 1

=======================================================================