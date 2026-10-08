```tla
MODULE SmallPlusCalAlg
EXTENDS Naturals, Integers

CONSTANTS 
    InitX \* The initial value of x in the range 1..10

VARIABLES x, pc

Init == /\ x = InitX
        /\ pc = "Start"

Next ==
    \/ /\ pc = "Start"
       /\ x ^ 2 <= 100
       /\ pc' = "Done"
       /\ x' = x
    \/ /\ pc = "Done"
       /\ UNCHANGED <<x, pc>>

Spec ==
    /\ Init
    /\ [][Next]_<<x, pc>>
    /\ WF_next(<<x, pc>>)

Termination ==
    <>[](pc = "Done")

====

THEOREM Spec => []<>(pc = "Done")
```