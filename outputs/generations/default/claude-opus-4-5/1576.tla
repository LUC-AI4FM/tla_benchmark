-------------------------------- MODULE ConcurrentQueue --------------------------------
EXTENDS Integers, Sequences

CONSTANTS Procs, Val, N

VARIABLES queue, rV, pc

vars == <<queue, rV, pc>>

\* Possible return values
ReturnValues == {"okay", "full", "empty", "null"} \cup Val

\* Initial state
Init ==
    /\ queue = <<>>
    /\ rV = [p \in Procs |-> "null"]
    /\ pc = [p \in Procs |-> "Ready"]

\* Enqueue at the front of the queue
EnqueueFront(self, v) ==
    /\ pc[self] = "Ready"
    /\ IF Len(queue) < N
       THEN /\ queue' = <<v>> \o queue
            /\ rV' = [rV EXCEPT ![self] = "okay"]
       ELSE /\ queue' = queue
            /\ rV' = [rV EXCEPT ![self] = "full"]
    /\ pc' = [pc EXCEPT ![self] = "Ready"]

\* Enqueue at the back of the queue
EnqueueBack(self, v) ==
    /\ pc[self] = "Ready"
    /\ IF Len(queue) < N
       THEN /\ queue' = Append(queue, v)
            /\ rV' = [rV EXCEPT ![self] = "okay"]
       ELSE /\ queue' = queue
            /\ rV' = [rV EXCEPT ![self] = "full"]
    /\ pc' = [pc EXCEPT ![self] = "Ready"]

\* Dequeue from the head (front) of the queue
DequeueHead(self) ==
    /\ pc[self] = "Ready"
    /\ IF Len(queue) > 0
       THEN /\ rV' = [rV EXCEPT ![self] = Head(queue)]
            /\ queue' = Tail(queue)
       ELSE /\ rV' = [rV EXCEPT ![self] = "empty"]
            /\ queue' = queue
    /\ pc' = [pc EXCEPT ![self] = "Ready"]

\* Dequeue from the tail (back) of the queue
DequeueTail(self) ==
    /\ pc[self] = "Ready"
    /\ IF Len(queue) > 0
       THEN /\ rV' = [rV EXCEPT ![self] = queue[Len(queue)]]
            /\ queue' = SubSeq(queue, 1, Len(queue) - 1)
       ELSE /\ rV' = [rV EXCEPT ![self] = "empty"]
            /\ queue' = queue
    /\ pc' = [pc EXCEPT ![self] = "Ready"]

\* Process action: nondeterministically choose an operation
P(self) ==
    \/ \E v \in Val : EnqueueFront(self, v)
    \/ \E v \in Val : EnqueueBack(self, v)
    \/ DequeueHead(self)
    \/ DequeueTail(self)

\* Next-state relation
Next ==
    \E self \in Procs : P(self)

\* Fairness condition: weak fairness for each process
Fairness ==
    \A self \in Procs : WF_vars(P(self))

\* Temporal specification
Spec == Init /\ [][Next]_vars /\ Fairness

\* State constraint: bounds queue length by N
StateConstraint == Len(queue) <= N

\* Safety invariant: queue length never exceeds N
QueueBounded == Len(queue) <= N

\* Type invariant
TypeInvariant ==
    /\ queue \in Seq(Val)
    /\ Len(queue) <= N
    /\ rV \in [Procs -> ReturnValues]
    /\ pc \in [Procs -> {"Ready"}]

=============================================================================