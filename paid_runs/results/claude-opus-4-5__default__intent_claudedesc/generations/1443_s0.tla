---------------------------- MODULE PossibleFeatureTest ----------------------------
EXTENDS Integers, TLC

VARIABLES counter

\* Initial state: counter starts at 0
Init == counter = 0

\* Next state: increment counter modulo 3 (cycles through 0, 1, 2)
Next == counter' = (counter + 1) % 3

\* Specification with weak fairness to ensure progress
Spec == Init /\ [][Next]_counter /\ WF_counter(Next)

\* Predicate 1: Counter reaches value 2
ReachesTwo == counter = 2

\* Predicate 2: Counter equals 1
EqualsOne == counter = 1

\* Predicate 3: Wrap-around transition from 2 back to 0
WrapAround == counter = 2 /\ counter' = 0

\* _POSSIBLE directives for TLC to track if these predicates are ever satisfied
ReachesTwo_POSSIBLE == ReachesTwo
EqualsOne_POSSIBLE == EqualsOne
WrapAround_POSSIBLE == WrapAround

\* Postcondition to verify TLC recorded exactly one witness for each predicate
\* TLCGet("spec") returns a record with possibility tracking information
\* The _POSSIBLE predicates are tracked and their witness counts can be checked
Postcondition ==
    LET possibleCounts == TLCGet("spec").possibles
    IN /\ possibleCounts["ReachesTwo_POSSIBLE"] = 1
       /\ possibleCounts["EqualsOne_POSSIBLE"] = 1
       /\ possibleCounts["WrapAround_POSSIBLE"] = 1

\* Safety invariant: counter is always in valid range
TypeInvariant == counter \in 0..2

\* Liveness property: counter eventually reaches each value
EventuallyReachesTwo == <>ReachesTwo
EventuallyEqualsOne == <>EqualsOne
EventuallyWraps == <>(counter = 0 /\ counter' = (counter + 1) % 3)

===================================================================================