------------------------------- MODULE CoffeeCan --------------------------------

CONSTANTS
    InitBlackCount,
    InitWhiteCount

VARIABLES
    blackCount,
    whiteCount

ASSUME InitBlackCount \in Nat /\ InitWhiteCount \in Nat /\ InitBlackCount + InitWhiteCount > 0

Init == 
    /\ blackCount = InitBlackCount
    /\ whiteCount = InitWhiteCount

Next ==
    \/ /\ blackCount >= 2
       /\ blackCount' = blackCount - 1
       /\ whiteCount' = whiteCount
    \/ /\ whiteCount >= 2
       /\ blackCount' = blackCount + 1
       /\ whiteCount' = whiteCount - 2
    \/ /\ blackCount > 0 /\ whiteCount > 0
       /\ blackCount' = blackCount - 1
       /\ whiteCount' = whiteCount

Spec == Init /\ [][Next]_<<blackCount, whiteCount>>

Safety ==
    \A s, s' \in State: 
        \/ s.blackCount + s.whiteCount < 2
        \/ (s'.blackCount + s'.whiteCount) = (s.blackCount + s.whiteCount - 1)

Termination ==
    <>[](blackCount + whiteCount = 1)

ParityInvariant ==
    [](whiteCount % 2 = InitWhiteCount % 2)

FinalState ==
    <>(/\ blackCount + whiteCount = 1
       /\ (whiteCount = 0 <-> InitWhiteCount % 2 = 0))

FairnessAssumption ==
    WF_next(<<blackCount, whiteCount>>)

THEOREM Spec => []Safety

THEOREM Spec => Termination

THEOREM Spec => ParityInvariant

THEOREM Spec => FinalState

=============================================================================