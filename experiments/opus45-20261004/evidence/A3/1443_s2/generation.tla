---------------------------- MODULE ModuloCounter ----------------------------

EXTENDS Integers, TLC

VARIABLES x

\* Helper predicates
IsOne == x = 1
AllDone == x = 2
WrapAround == x = 2 /\ x' = 0

\* Initial state
Init == x = 0

\* Next state relation - advance modulo 3
Next == x' = (x + 1) % 3

\* Temporal specification with stuttering
Spec == Init /\ [][Next]_x

\* Safety invariant - x is always in valid range
TypeInvariant == x \in 0..2

\* TLC-specific check for named-state coverage
\* This checks that the three predicates IsOne, AllDone, and WrapAround are each counted
TLCCoverageCheck ==
    LET isOneCount == TLCGet("stats").coverage["IsOne"]
        allDoneCount == TLCGet("stats").coverage["AllDone"]
        wrapAroundCount == TLCGet("stats").coverage["WrapAround"]
    IN /\ isOneCount = 1
       /\ allDoneCount = 1
       /\ wrapAroundCount = 1

=============================================================================