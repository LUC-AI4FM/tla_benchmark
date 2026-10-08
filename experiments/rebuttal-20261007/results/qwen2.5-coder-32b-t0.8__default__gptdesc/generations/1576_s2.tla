------------------------------ MODULE ConcurrentQueue ------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS Procs, Val, N

VARIABLES queue, rV

Init == /\ queue = << >>
        /\ \A p \in Procs : rV[p] = "null"

EnqueueFront(p, v) ==
    /\ queue' = <<v>> \o queue
    /\ rV' = [rV EXCEPT ![p] = "okay"]
    /\ UNCHANGED <<Procs, Val>>

EnqueueBack(p, v) ==
    /\ queue' = queue \o <<v>>
    /\ rV' = [rV EXCEPT ![p] = "okay"]
    /\ UNCHANGED <<Procs, Val>>

DequeueFront(p) ==
    /\ Len(queue) > 0
    /\ LET val == queue[1] IN
        /\ queue' = Tail(queue)
        /\ rV' = [rV EXCEPT ![p] = val]
        /\ UNCHANGED <<Procs, Val>>

DequeueTail(p) ==
    /\ Len(queue) > 0
    /\ LET val == queue[Len(queue)] IN
        /\ queue' = Head(queue, Len(queue)-1)
        /\ rV' = [rV EXCEPT ![p] = val]
        /\ UNCHANGED <<Procs, Val>>

QueueFull ==
    /\ Len(queue) >= N

P(p) ==
    \/ /\ ~QueueFull
       /\ \/ EnqueueFront(p, CHOOSE v \in Val : TRUE)
          \/ EnqueueBack(p, CHOOSE v \in Val : TRUE)
    \/ QueueFull
       /\ rV' = [rV EXCEPT ![p] = "full"]
       /\ UNCHANGED queue
    \/ /\ Len(queue) > 0
       /\ \/ DequeueFront(p)
          \/ DequeueTail(p)
    \/ /\ Len(queue) = 0
       /\ rV' = [rV EXCEPT ![p] = "empty"]
       /\ UNCHANGED queue

Next ==
    \E p \in Procs : P(p)

Spec == Init /\ [][Next]_<<Procs, Val>>

Fairness ==
    WF_next(\A p \in Procs: P(p))

QueueBound ==
    Len(queue) <= N

THEOREM Spec => []QueueBound
=============================================================================