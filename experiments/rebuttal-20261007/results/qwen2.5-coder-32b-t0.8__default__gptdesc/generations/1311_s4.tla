```tla
MODULE GCDBySubtraction

EXTENDS Integers, TLC

CONSTANTS 
    LowerBound, UpperBound  \* LowerBound = 1, UpperBound = 50

VARIABLES u, v, pc

Init == /\ u = 24
        /\ v \in LowerBound .. UpperBound
        /\ pc = "Start"

Step ==
    \/ /\ pc = "Start"
       /\ u < v
       /\ pc' = "Swap"
       /\ u' = v
       /\ v' = u'
    \/ /\ pc = "Start"
       /\ u >= v
       /\ pc' = "Subtract"
       /\ u' = u - v
       /\ v' = v'
    \/ /\ pc = "Swap"
       /\ u < v
       /\ pc' = "Swap"
       /\ u' = v
       /\ v' = u'
    \/ /\ pc = "Swap"
       /\ u >= v
       /\ pc' = "Subtract"
       /\ u' = u - v
       /\ v' = v'
    \/ /\ pc = "Subtract"
       /\ u # 0
       /\ pc' = "Start"
       /\ u' = u - v
       /\ v' = v'
    \/ /\ pc = "Subtract"
       /\ u = 0
       /\ pc' = "Done"
       /\ u' = u'
       /\ v' = v'

Next ==
    Step \/ (pc = "Done" /\ UNCHANGED <<u, v>>)

Spec ==
    /\ Init
    /\ [][Next]_<<u, v, pc>>
    /\ WF_pc(Step)
```

Note: The fairness condition `WF_pc(Step)` is included to ensure that the system makes progress through the states defined in `Step`. This condition ensures that if a step is enabled infinitely often, it will be taken infinitely often.