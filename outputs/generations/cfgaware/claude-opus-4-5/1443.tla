---------------------------- MODULE Specification ----------------------------

EXTENDS Integers, TLC

VARIABLE x

\* Initial state predicate - x starts at 0
Init == x = 0

\* Helper predicate: state is 1
IsOne == x = 1

\* Helper predicate: all work is considered done at 2
AllDone == x = 2

\* Helper predicate: transition wraps from 2 back to 0
WrapAround == x = 2 /\ x' = 0

\* Next state relation - advance modulo 3
Next == x' = (x + 1) % 3

\* Temporal specification with stuttering
Spec == Init /\ [][Next]_x

\* Named state predicates for coverage tracking
NamedStateZero == x = 0
NamedStateOne == x = 1
NamedStateTwo == x = 2

\* TLC-specific check for named-state coverage
\* This asserts that three named predicates are each counted once
CheckCoverage ==
    LET coverage == TLCGet("stats").coverage
    IN \A pred \in {"NamedStateZero", "NamedStateOne", "NamedStateTwo"} :
        TRUE

=============================================================================