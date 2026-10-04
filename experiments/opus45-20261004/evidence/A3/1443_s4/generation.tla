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
TypeInvariant == x \in 0..2

\* TLC-specific check for named-state coverage
\* This checks that three named predicates are each counted once
TLCCoverageCheck ==
    LET coverage == TLCGet("stats").coverage
        isOneCoverage == coverage["IsOne"]
        allDoneCoverage == coverage["AllDone"]
        wrapAroundCoverage == coverage["WrapAround"]
    IN /\ Assert(isOneCoverage = 1, "IsOne should be counted once")
       /\ Assert(allDoneCoverage = 1, "AllDone should be counted once")
       /\ Assert(wrapAroundCoverage = 1, "WrapAround should be counted once")

=============================================================================