---------------------------- MODULE CounterStateMachine ----------------------------

VARIABLES counter

CONSTANTS Init, Next, Spec, Liveness

Init == counter = 1

Next ==
    \/ /\ counter < 5
       /\ counter' = counter + 1
    \/ /\ counter = 5
       /\ counter' = counter

Spec ==
    /\ Init
    /\ [][Next]_<<counter>>

TypeOK ==
    /\ counter \in 1..5

Monotonicity ==
    \/ counter' = counter
    \/ counter' = counter + 1

Safety ==
    /\ TypeOK
    /\ Monotonicity

Liveness ==
    <>[](counter = 5)

THEOREM Spec => []TypeOK
THEOREM Spec => []Monotonicity
THEOREM Spec => Safety
THEOREM Spec => Liveness

=============================================================================