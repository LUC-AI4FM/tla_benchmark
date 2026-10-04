---------------------------- MODULE spec ----------------------------
EXTENDS Integers, Sequences

CONSTANTS Val, N, Procs

VARIABLES queue, rV, pc

vars == <<queue, rV, pc>>

Init ==
    /\ queue = <<>>
    /\ rV = [p \in Procs |-> "null"]
    /\ pc = [p \in Procs |-> "Loop"]

EnqueueFront(self) ==
    /\ pc[self] = "Loop"
    /\ Len(queue) < N
    /\ \E v \in Val:
        /\ queue' = <<v>> \o queue
        /\ rV' = [rV EXCEPT ![self] = "okay"]
    /\ pc' = [pc EXCEPT ![self] = "Loop"]

EnqueueBack(self) ==
    /\ pc[self] = "Loop"
    /\ Len(queue) < N
    /\ \E v \in Val:
        /\ queue' = Append(queue, v)
        /\ rV' = [rV EXCEPT ![self] = "okay"]
    /\ pc' = [pc EXCEPT ![self] = "Loop"]

EnqueueFullFront(self) ==
    /\ pc[self] = "Loop"
    /\ Len(queue) >= N
    /\ queue' = queue
    /\ rV' = [rV EXCEPT ![self] = "full"]
    /\ pc' = [pc EXCEPT ![self] = "Loop"]

EnqueueFullBack(self) ==
    /\ pc[self] = "Loop"
    /\ Len(queue) >= N
    /\ queue' = queue
    /\ rV' = [rV EXCEPT ![self] = "full"]
    /\ pc' = [pc EXCEPT ![self] = "Loop"]

DequeueHead(self) ==
    /\ pc[self] = "Loop"
    /\ Len(queue) > 0
    /\ rV' = [rV EXCEPT ![self] = Head(queue)]
    /\ queue' = Tail(queue)
    /\ pc' = [pc EXCEPT ![self] = "Loop"]

DequeueTail(self) ==
    /\ pc[self] = "Loop"
    /\ Len(queue) > 0
    /\ rV' = [rV EXCEPT ![self] = queue[Len(queue)]]
    /\ queue' = SubSeq(queue, 1, Len(queue) - 1)
    /\ pc' = [pc EXCEPT ![self] = "Loop"]

DequeueEmpty(self) ==
    /\ pc[self] = "Loop"
    /\ Len(queue) = 0
    /\ queue' = queue
    /\ rV' = [rV EXCEPT ![self] = "empty"]
    /\ pc' = [pc EXCEPT ![self] = "Loop"]

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

TypeInvariant ==
    /\ queue \in Seq(Val)
    /\ Len(queue) <= N
    /\ rV \in [Procs -> Val \cup {"okay", "full", "empty", "null"}]
    /\ pc \in [Procs -> {"Loop"}]

=========================================================================