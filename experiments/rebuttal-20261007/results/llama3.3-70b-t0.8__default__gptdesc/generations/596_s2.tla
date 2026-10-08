```
MODULE OneVariableTransitionSystem
EXTENDS Integers

CONSTANTS 

VARIABLES x

Init == (x = 0)

Next == (x = 0) /\ (x' = 1 \/ x' = 2) 
       \/ (x /= 0) /\ (x' = 0)

Spec == Init /\ [][Next]_x /\ WF_x(Next)

StabilizeAwayFrom1 == <>[]<>(x /= 1)
StabilizeAwayFrom2 == <>[]<>(x /= 2)
ReturnToZero == []<>((x = 0) /\ (x' = 0))
NotStabilizeAwayFrom1 == ~StabilizeAwayFrom1

THEOREM Spec => StabilizeAwayFrom1
THEOREM Spec => StabilizeAwayFrom2
THEOREM Spec => ReturnToZero
THEOREM Spec => NotStabilizeAwayFrom1
```