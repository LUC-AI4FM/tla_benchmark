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

\* TLC-specific check for named-state coverage
\* This checks that each of the three predicates (IsOne, AllDone, WrapAround equivalent states) 
\* are visited during model checking
TLCCoverageCheck ==
    LET coverage == TLCGet("stats").coverage
        isOneCnt == coverage["IsOne"]
        allDoneCnt == coverage["AllDone"]
        wrapAroundCnt == coverage["WrapAround"]
    IN isOneCnt = 1 /\ allDoneCnt = 1 /\ wrapAroundCnt = 1

===============================================================================