------------------------------- MODULE ConcurrentQueue -------------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Procs, Val, N

VARIABLES queue, rV

Init == /\ queue = << >>
        /\ rV \in [Procs -> {NULL}]
        
EnqueueFront(self) ==
    \/ /\ queue' = << self >> \o queue
       /\ rV' = [rV EXCEPT ![self] = "okay"]
    \/ /\ queue' = queue
       /\ rV' = [rV EXCEPT ![self] = "full"]

EnqueueBack(self) ==
    \/ /\ queue' = queue \o << self >>
       /\ rV' = [rV EXCEPT ![self] = "okay"]
    \/ /\ queue' = queue
       /\ rV' = [rV EXCEPT ![self] = "full"]

DequeueFront(self) ==
    \/ /\ queue /= << >>
       /\ LET v == Head(queue)
          IN queue' = Tail(queue)
             /\ rV' = [rV EXCEPT ![self] = v]
    \/ /\ queue = << >>
       /\ rV' = [rV EXCEPT ![self] = "empty"]

DequeueTail(self) ==
    \/ /\ queue /= << >>
       /\ LET v == Last(queue)
          IN queue' = Front(queue, Len(queue) - 1)
             /\ rV' = [rV EXCEPT ![self] = v]
    \/ /\ queue = << >>
       /\ rV' = [rV EXCEPT ![self] = "empty"]

P(self) ==
    \/ EnqueueFront(self)
    \/ EnqueueBack(self)
    \/ DequeueFront(self)
    \/ DequeueTail(self)

Next ==
    \E self \in Procs : P(self)

Spec == Init /\ [][Next]_<<Procs>> /\ WF_[<<Procs>>]P

QueueLengthBound ==
    Len(queue) <= N

THEOREM Spec => []QueueLengthBound
================================================================================