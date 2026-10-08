```
MODULE OneVariableTransitionSystem
EXTENDS Integers

CONSTANTS None

VARIABLES x

Init == (x = 0)

Next == (x = 0) /\ (x' = 1 \/ x' = 2) 
        \/ (x /= 0) /\ (x' = 0)

Spec == Init /\ [][Next]_x
       /\ WF_x(Next)

THEOREM Spec => <>[]~(x = 1)
THEOREM Spec => <>[]~(x = 2)
THEOREM Spec => []<>((x = 0) /\ (x' = 0))
THEOREM Spec => ~([]<>(x = 1))
THEOREM Spec => <<x>>_x

Postcondition == 
  \E s \in [0..10] : 
    /\ x[s] = 0
    /\ \A t \in [s+1..9] : (x[t] /= 0) => (x[t+1] = 0)
```