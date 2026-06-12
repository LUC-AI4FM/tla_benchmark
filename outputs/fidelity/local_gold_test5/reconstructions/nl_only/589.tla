MODULE CyclicCounter

EXTENDS Naturals, TLC

CONSTANTS MaxValue

VARIABLES x

Init == /\ x = 0
        /\ TLCSet(42, x)

Next == \/ /\ x < MaxValue
             /\ x' = x + 1
             /\ TLCSet(42, x')
         \/ /\ x = MaxValue
             /\ x' = 0
             /\ TLCSet(42, x')

Spec == Init /\ [][Next]_<<x>> /\ WF_next(Next)

Liveness == <>[](x = 1)

Postconditions == TLCGet(42) = x

CompleteSpec == Spec /\ Liveness /\ Postconditions

MaxValue == 5