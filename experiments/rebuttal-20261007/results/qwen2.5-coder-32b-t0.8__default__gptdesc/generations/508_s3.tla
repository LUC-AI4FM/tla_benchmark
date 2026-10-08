```tla
MODULE SmallPlusCalAlgorithm

EXTENDS Integers, TLC

CONSTANTS 
    InitVal \in 1..10

VARIABLES x, pc

Init == /\ x = InitVal
        /\ pc = "Start"

Next ==
    \/ /\ pc = "Start"
       /\ x ^ 2 <= 100
       /\ pc' = "Done"
       /\ x' = x
    \/ /\ pc = "Done"
       /\ UNCHANGED <<x, pc>>

Spec == Init /\ [][Next]_<<x, pc>> /\ WF_next(<<x, pc>>)

WF_next(vars) ==
    \A vars', \E v \in (DOMAIN vars) : vars' = [vars EXCEPT ![v] = vars[v]']

Termination ==
    <>[](pc = "Done")

THEOREM Spec => Termination
```