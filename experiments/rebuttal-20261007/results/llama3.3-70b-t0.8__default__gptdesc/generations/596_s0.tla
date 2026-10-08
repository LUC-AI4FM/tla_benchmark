```
MODULE OneVariableTransitionSystem
EXTENDS Integers

CONSTANTS None

VARIABLES x

Init == (x = 0)

Next == (x = 0) \/ ((x /= 0) /\ (x' = 0))
       \/ (x = 0 /\ (x' = 1 \/ x' = 2))

Spec == Init /\ [][Next]_x
       /\ WF_x(Next)

StabilizeAwayFrom1 == <>[]<>(x /= 1)
StabilizeAwayFrom2 == <>[]<>(x /= 2)
ReturnToZeroRepeatedly == []<> (x = 0)
NegationOfProperty == ~[]<>(x /= 1)
Postcondition == \E s \in [1, 2] : <<s, x>> \in TLC_trace

THEOREM Spec => StabilizeAwayFrom1
THEOREM Spec => StabilizeAwayFrom2
THEOREM Spec => ReturnToZeroRepeatedly
THEOREM Spec => NegationOfProperty
THEOREM Spec => Postcondition
```