---------------------------- MODULE PossibleCheck ----------------------------
EXTENDS Naturals, TLC, FiniteSets

VARIABLE x

vars == <<x>>

Init == x = 0

Next == x' = (x + 1) % 3

Spec == Init /\ [][Next]_vars

\* Predicate: the counter reaches 2
AllDone == x = 2

\* Predicate: the counter equals 1
AtOne == x = 1

\* Predicate: wrap-around transition from 2 back to 0
WrapAround == x = 2 /\ x' = 0

\* Predicates TLC should track to see whether each is ever satisfied
_POSSIBLE == <<AllDone, AtOne, WrapAround>>

\* Postcondition: TLC recorded exactly one witness for each of the three predicates
PossibleCounts ==
    LET p == TLCGet("possible")
    IN  /\ Cardinality(DOMAIN p) = 3
        /\ \A i \in DOMAIN p : p[i] = 1

=============================================================================