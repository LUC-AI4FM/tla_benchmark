---------------------------- MODULE ConcurrentQueue ----------------------------
EXTENDS Integers, Sequences

CONSTANTS Procs, Val, N

VARIABLES queue, rV, pc

vars == <<queue, rV, pc>>

Init ==
    /\ queue = <<>>
    /\ rV = [p \in Procs |-> "null"]
    /\ pc = [p \in Procs |-> "Choose"]

EnqueueFront(self) ==
    /\ pc[self] = "EnqueueFront"
    /\ IF Len(queue) < N
       THEN /\ \E v \in Val:
                 queue' = <<v>> \o queue
            /\ rV' = [rV EXCEPT ![self] = "okay"]
       ELSE /\ rV' = [rV EXCEPT ![self] = "full"]
            /\ queue' = queue
    /\ pc' = [pc EXCEPT ![self] = "Choose"]

EnqueueBack(self) ==
    /\ pc[self] = "EnqueueBack"
    /\ IF Len(queue) < N
       THEN /\ \E v \in Val:
                 queue' = Append(queue, v)
            /\ rV' = [rV EXCEPT ![self] = "okay"]
       ELSE /\ rV' = [rV EXCEPT ![self] = "full"]
            /\ queue' = queue
    /\ pc' = [pc EXCEPT ![self] = "Choose"]

DequeueHead(self) ==
    /\ pc[self] = "DequeueHead"
    /\ IF Len(queue) > 0
       THEN /\ rV' = [rV EXCEPT ![self] = Head(queue)]
            /\ queue' = Tail(queue)
       ELSE /\ rV' = [rV EXCEPT ![self] = "empty"]
            /\ queue' = queue
    /\ pc' = [pc EXCEPT ![self] = "Choose"]

DequeueTail(self) ==
    /\ pc[self] = "DequeueTail"
    /\ IF Len(queue) > 0
       THEN /\ rV' = [rV EXCEPT ![self] = queue[Len(queue)]]
            /\ queue' = SubSeq(queue, 1, Len(queue) - 1)
       ELSE /\ rV' = [rV EXCEPT ![self] = "empty"]
            /\ queue' = queue
    /\ pc' = [pc EXCEPT ![self] = "Choose"]

Choose(self) ==
    /\ pc[self] = "Choose"
    /\ \/ pc' = [pc EXCEPT ![self] = "EnqueueFront"]
       \/ pc' = [pc EXCEPT ![self] = "EnqueueBack"]
       \/ pc' = [pc EXCEPT ![self] = "DequeueHead"]
       \/ pc' = [pc EXCEPT ![self] = "DequeueTail"]
    /\ queue' = queue
    /\ rV' = rV

P(self) ==
    \/ Choose(self)
    \/ EnqueueFront(self)
    \/ EnqueueBack(self)
    \/ DequeueHead(self)
    \/ DequeueTail(self)

Next ==
    \E self \in Procs: P(self)

Fairness ==
    \A self \in Procs: WF_vars(P(self))

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

StateConstraint ==
    Len(queue) <= N

TypeInvariant ==
    /\ queue \in Seq(Val)
    /\ Len(queue) <= N
    /\ rV \in [Procs -> Val \cup {"okay", "full", "empty", "null"}]
    /\ pc \in [Procs -> {"Choose", "EnqueueFront", "EnqueueBack", "DequeueHead", "DequeueTail"}]

QueueBoundInvariant ==
    Len(queue) <= N

=============================================================================