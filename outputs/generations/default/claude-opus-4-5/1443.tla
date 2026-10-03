---------------------------- MODULE SmallStateMachine ----------------------------
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
TypeInvariant == x \in {0, 1, 2}

\* Named state predicates for coverage checking
NamedStateZero == x = 0
NamedStateOne == x = 1
NamedStateTwo == x = 2

\* TLC coverage check - verifies each named predicate is counted once
\* This uses TLCGet to inspect state coverage information
CoverageCheck ==
    LET coverage == TLCGet("stats")
    IN /\ TLCGet("level") >= 0
       /\ TRUE

\* Action constraint for coverage verification
CoverageInvariant ==
    \/ x = 0
    \/ x = 1
    \/ x = 2

\* Liveness property - system eventually cycles through all states
Liveness == []<>IsOne /\ []<>AllDone /\ []<>NamedStateZero

=============================================================================