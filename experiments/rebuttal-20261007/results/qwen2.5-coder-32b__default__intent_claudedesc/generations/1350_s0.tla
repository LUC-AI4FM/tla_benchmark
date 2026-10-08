------------------------------- MODULE CounterSpec -------------------------------
EXTENDS Naturals, TLC

CONSTANTS MaxValue

VARIABLES counter

Init == counter = 1

Next ==
    \/ /\ counter < MaxValue
       /\ counter' = counter + 1
    \/ /\ counter = MaxValue
       /\ counter' = counter

Spec ==
    /\ Init
    /\ [][Next]_<<counter>>
    /\ WF_[Next]_<<counter>>

Stability == [](counter = MaxValue => []<>(counter' = counter))

Liveness == <>(counter = MaxValue)

SpecWithProperties ==
    /\ Spec
    /\ Stability
    /\ Liveness

=============================================================================