---- MODULE ConcurrentQueue ----
EXTENDS Sequences, TLC, Integers

CONSTANTS Procs, Val, N

VARIABLES queue, rV

vars == <<queue, rV>>

ASSUME IsFiniteSet(Procs)
ASSUME IsFiniteSet(Val)
ASSUME N \in Nat
ASSUME \A v \in {"okay", "full", "empty", "null"}: v \notin Val

Init ==
    /\ queue = <<>>
    /\ rV = [p \in Procs |-> "null"]

EnqueueFront(self, v) ==
    /\ IF Len(queue) < N
       THEN /\ queue' = <v> \o queue
            /\ rV' = [rV EXCEPT ![self] = "okay"]
       ELSE /\ queue' = queue
            /\ rV' = [rV EXCEPT ![self] = "full"]

EnqueueBack(self, v) ==
    /\ IF Len(queue) < N
       THEN /\ queue' = Append(queue, v)
            /\ rV' = [rV EXCEPT ![self] = "okay"]
       ELSE /\ queue' = queue
            /\ rV' = [rV EXCEPT ![self] = "full"]

DequeueHead(self) ==
    /\ IF Len(queue) > 0
       THEN /\ LET dequeuedVal == Head(queue)
            IN  /\ queue' = Tail(queue)
                /\ rV' = [rV EXCEPT ![self] = dequeuedVal]
       ELSE /\ queue' = queue
            /\ rV' = [rV EXCEPT ![self] = "empty"]

DequeueTail(self) ==
    /\ IF Len(queue) > 0
       THEN /\ LET dequeuedVal == queue[Len(queue)]
            IN  /\ queue' = SubSeq(queue, 1, Len(queue) - 1)
                /\ rV' = [rV EXCEPT ![self] = dequeuedVal]
       ELSE /\ queue' = queue
            /\ rV' = [rV EXCEPT ![self] = "empty"]

P(self) ==
    \/ (\E v \in Val: EnqueueFront(self, v))
    \/ (\E v \in Val: EnqueueBack(self, v))
    \/ DequeueHead(self)
    \/ DequeueTail(self)

Next == \E self \in Procs: P(self)

StateConstraint == Len(queue) <= N

Fairness == \A self \in Procs: WF_vars(P(self))

Spec == Init /\ [][Next]_vars /\ []StateConstraint /\ Fairness

=============================================================================