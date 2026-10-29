---------------------------- MODULE ConcurrentQueue ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Procs, Val, N, null

ASSUME /\ N \in Nat
       /\ null \notin Val

VARIABLES queue, rV, pc

vars == <<queue, rV, pc>>

ProcSet == Procs

RetVals == {"okay", "full", "empty", null} \cup Val

Init == /\ queue = << >>
        /\ rV = [self \in Procs |-> null]
        /\ pc = [self \in ProcSet |-> "Loop"]

EnqFront(self) ==
    \E v \in Val :
        IF Len(queue) < N
           THEN /\ queue' = <<v>> \o queue
                /\ rV' = [rV EXCEPT ![self] = "okay"]
           ELSE /\ queue' = queue
                /\ rV' = [rV EXCEPT ![self] = "full"]

EnqBack(self) ==
    \E v \in Val :
        IF Len(queue) < N
           THEN /\ queue' = Append(queue, v)
                /\ rV' = [rV EXCEPT ![self] = "okay"]
           ELSE /\ queue' = queue
                /\ rV' = [rV EXCEPT ![self] = "full"]

DeqHead(self) ==
    /\ Len(queue) > 0
    /\ rV' = [rV EXCEPT ![self] = Head(queue)]
    /\ queue' = Tail(queue)

DeqTail(self) ==
    /\ Len(queue) > 0
    /\ rV' = [rV EXCEPT ![self] = queue[Len(queue)]]
    /\ queue' = SubSeq(queue, 1, Len(queue) - 1)

Loop(self) ==
    /\ pc[self] = "Loop"
    /\ \/ EnqFront(self)
       \/ EnqBack(self)
       \/ DeqHead(self)
       \/ DeqTail(self)
    /\ pc' = [pc EXCEPT ![self] = "Loop"]

P(self) == Loop(self)

Next == \E self \in Procs : P(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(P(self))

\* State constraint bounding the queue length
StateConstraint == Len(queue) <= N

\* Safety invariants
TypeOK == /\ queue \in Seq(Val)
          /\ rV \in [Procs -> RetVals]
          /\ pc \in [ProcSet -> {"Loop"}]

BoundedQueue == Len(queue) <= N

=============================================================================