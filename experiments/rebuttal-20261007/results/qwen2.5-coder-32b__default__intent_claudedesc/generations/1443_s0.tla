------------------------------- MODULE CounterSpec -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS MaxValue

VARIABLES counter

Init == counter = 0

Next ==
    /\ counter' \in {0, 1, 2}
    /\ counter' = (counter + 1) % (MaxValue + 1)

Spec ==
    /\ Init
    /\ [][Next]_<<counter>>

CONSTANTS Pred2, Pred1, WrapAround

Pred2 == counter = 2
Pred1 == counter = 1
WrapAround == /\ counter = MaxValue
               /\ counter' = 0

POSSIBLE Pred2
POSSIBLE Pred1
POSSIBLE WrapAround

PostCondition ==
    /\ _POSSIBLY(Pred2) = 1
    /\ _POSSIBLY(Pred1) = 1
    /\ _POSSIBLY(WrapAround) = 1

CompleteSpec == Spec /\ <>[]<>(PostCondition)

=============================================================================