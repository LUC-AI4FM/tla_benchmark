---------------------------- MODULE ConcurrentQueue ----------------------------
EXTENDS Integers, Sequences

CONSTANTS Val, Procs, N, null, okay, full, empty

VARIABLES queue, rV, pc

vars == <<queue, rV, pc>>

Init ==
    /\ queue = <<>>
    /\ rV = [p \in Procs |-> null]
    /\ pc = [p \in Procs |-> "start"]

EnqueueFront(self) ==
    /\ pc[self] = "start"
    /\ Len(queue) < N
    /\ \E v \in Val:
        /\ queue' = <<v>> \o queue
        /\ rV' = [rV EXCEPT ![self] = okay]
    /\ pc' = [pc EXCEPT ![self] = "start"]

EnqueueBack(self) ==
    /\ pc[self] = "start"
    /\ Len(queue) < N
    /\ \E v \in Val:
        /\ queue' = Append(queue, v)
        /\ rV' = [rV EXCEPT ![self] = okay]
    /\ pc' = [pc EXCEPT ![self] = "start"]

EnqueueFullFront(self) ==
    /\ pc[self] = "start"
    /\ Len(queue) >= N
    /\ queue' = queue
    /\ rV' = [rV EXCEPT ![self] = full]
    /\ pc' = [pc EXCEPT ![self] = "start"]

EnqueueFullBack(self) ==
    /\ pc[self] = "start"
    /\ Len(queue) >= N
    /\ queue' = queue
    /\ rV' = [rV EXCEPT ![self] = full]
    /\ pc' = [pc EXCEPT ![self] = "start"]

DequeueHead(self) ==
    /\ pc[self] = "start"
    /\ Len(queue) > 0
    /\ rV' = [rV EXCEPT ![self] = Head(queue)]
    /\ queue' = Tail(queue)
    /\ pc' = [pc EXCEPT ![self] = "start"]

DequeueTail(self) ==
    /\ pc[self] = "start"
    /\ Len(queue) > 0
    /\ rV' = [rV EXCEPT ![self] = queue[Len(queue)]]
    /\ queue' = SubSeq(queue, 1, Len(queue) - 1)
    /\ pc' = [pc EXCEPT ![self] = "start"]

DequeueEmpty(self) ==
    /\ pc[self] = "start"
    /\ Len(queue) = 0
    /\ queue' = queue
    /\ rV' = [rV EXCEPT ![self] = empty]
    /\ pc' = [pc EXCEPT ![self] = "start"]

P(self) ==
    \/ EnqueueFront(self)
    \/ EnqueueBack(self)
    \/ EnqueueFullFront(self)
    \/ EnqueueFullBack(self)
    \/ DequeueHead(self)
    \/ DequeueTail(self)
    \/ DequeueEmpty(self)

Next ==
    \E self \in Procs: P(self)

Fairness ==
    \A self \in Procs: WF_vars(P(self))

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

StateConstraint == Len(queue) <= N

================================================================================