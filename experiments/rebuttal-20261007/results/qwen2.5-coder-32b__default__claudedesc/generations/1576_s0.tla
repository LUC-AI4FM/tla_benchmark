------------------------------- MODULE SharedQueue -------------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Val, Procs, N

VARIABLES queue, rV

Init == /\ queue = << >>
        /\ \A p \in Procs : rV[p] = "null"

Enqueue ==
    \/ /\ queue' = Append(queue, CHOOSE v \in Val: TRUE)
       \/ queue' = Prepend(CHOOSE v \in Val: TRUE, queue)
       \/ queue' = queue
Dequeue ==
    \/ /\ queue /= << >>
       /\ (/\ rV' = Head(queue)
           /\ queue' = Tail(queue))
       \/ (/\ rV' = Last(queue)
           /\ queue' = Front(queue, Len(queue) - 1))
    \/ /\ queue = << >>
       /\ rV' = "empty"
       /\ queue' = queue

Operation ==
    \E p \in Procs :
        \/ /\ rV[p] = "null"
           /\ (Enqueue \/ Dequeue)
           /\ \A q \in Procs \ {p} : rV'[q] = rV[q]
        \/ /\ rV[p] /= "null"
           /\ rV'[p] = "null"
           /\ queue' = queue

Next == Operation

Spec ==
    /\ Init
    /\ [][Next]_<<queue, rV>>
    /\ WF_<<queue, rV>>(Operation)

StateConstraint ==
    Len(queue) \leq N

CONSTRAINT StateConstraint

INSTANCE Fairness[Procs]

=============================================================================