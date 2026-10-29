------------------------------- MODULE DequeQueue -------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Val, Procs, N, null

VARIABLES queue, rV, pc

vars == << queue, rV, pc >>

ProcSet == Procs

Init ==
    /\ queue = << >>
    /\ rV = [p \in Procs |-> null]
    /\ pc = [p \in ProcSet |-> "L1"]

\* Enqueue: choose a value, then append to the back, prepend to the front,
\* or decline with "full".
Enq(self) ==
    \E v \in Val :
        \/ /\ queue' = Append(queue, v)
           /\ rV' = [rV EXCEPT ![self] = "ok"]
        \/ /\ queue' = << v >> \o queue
           /\ rV' = [rV EXCEPT ![self] = "ok"]
        \/ /\ rV' = [rV EXCEPT ![self] = "full"]
           /\ UNCHANGED queue

\* Dequeue: if non-empty, remove and return the head or the tail;
\* otherwise return "empty".
Deq(self) ==
    IF queue /= << >>
    THEN \/ /\ rV' = [rV EXCEPT ![self] = Head(queue)]
            /\ queue' = Tail(queue)
         \/ /\ rV' = [rV EXCEPT ![self] = queue[Len(queue)]]
            /\ queue' = SubSeq(queue, 1, Len(queue) - 1)
    ELSE /\ rV' = [rV EXCEPT ![self] = "empty"]
         /\ UNCHANGED queue

L1(self) ==
    /\ pc[self] = "L1"
    /\ \/ Enq(self)
       \/ Deq(self)
    /\ pc' = [pc EXCEPT ![self] = "L2"]

L2(self) ==
    /\ pc[self] = "L2"
    /\ rV' = [rV EXCEPT ![self] = null]
    /\ pc' = [pc EXCEPT ![self] = "L1"]
    /\ UNCHANGED queue

proc(self) == L1(self) \/ L2(self)

Next == \E self \in Procs : proc(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(proc(self))

Constraint == Len(queue) <= N

TypeOK ==
    /\ queue \in Seq(Val)
    /\ rV \in [Procs -> Val \cup {null, "ok", "full", "empty"}]
    /\ pc \in [Procs -> {"L1", "L2"}]

=============================================================================