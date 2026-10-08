------------------------------ MODULE SmallStateMachine ------------------------------

EXTENDS Naturals, TLC

CONSTANTS StateNames

VARIABLES x

Init == x = 0

Next == \/ /\ x < 2
            /\ x' = x + 1
         \/ /\ x = 2
            /\ x' = 0

StateIsOne(x) == x = 1
AllWorkDone(x) == x = 2
WrapAround(x, x') == x = 2 /\ x' = 0

Spec ==
    /\ Init
    /\ [][Next]_<<x>>

Invariants ==
    /\ \/ x = 0
       \/ x = 1
       \/ x = 2

LivenessProperties ==
    <>[](AllWorkDone(x))

Fairness ==
    WF_next(Next)

TLCStateCoverage ==
    TLCGet("NamedStateCoverage") = <<StateNames, <<1, 1, 1>>>> 

=============================================================================