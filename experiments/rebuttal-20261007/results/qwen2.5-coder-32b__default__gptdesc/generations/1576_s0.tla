------------------------------- MODULE ConcurrentQueue -------------------------------

EXTENDS Integers, Sequences, TLC

CONSTANTS Procs, Val, N

VARIABLES queue, rV

Init == /\ queue = << >>
        /\ \A p \in Procs : rV[p] = "null"

EnqueueFront ==
    /\ \E v \in Val : queue' = <<v>> \o queue
    /\ \A p \in Procs : rV'[p] = IF p = self THEN "okay" ELSE rV[p]

EnqueueBack ==
    /\ \E v \in Val : queue' = queue \o <<v>>
    /\ \A p \in Procs : rV'[p] = IF p = self THEN "okay" ELSE rV[p]

DequeueFront ==
    /\ Len(queue) > 0
    /\ queue' = Tail(queue)
    /\ rV'[self] = Head(queue)
    /\ \A p \in Procs \ {self} : rV'[p] = rV[p]

DequeueTail ==
    /\ Len(queue) > 0
    /\ queue' = SubSeq(queue, 1, Len(queue)-1)
    /\ rV'[self] = Last(queue)
    /\ \A p \in Procs \ {self} : rV'[p] = rV[p]

NoOp ==
    /\ queue' = queue
    /\ \A p \in Procs : rV'[p] = rV[p]

P(self) == 
    \/ EnqueueFront
    \/ EnqueueBack
    \/ DequeueFront
    \/ DequeueTail
    \/ NoOp

Next == \E p \in Procs : P(p)

Spec ==
    /\ Init
    /\ [][Next]_<<queue, rV>>
    /\ WF_<<queue, rV>>[P(self)]

QueueLengthBound == Len(queue) <= N

=============================================================================