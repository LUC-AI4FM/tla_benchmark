---------------------------- MODULE SharedDeque ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Val,    \* set of values that can be enqueued
          Procs,  \* set of process identifiers
          null,   \* distinguished sentinel value
          N       \* bound on queue length (used only in the state constraint)

ASSUME null \notin Val
ASSUME N \in Nat

VARIABLES queue,  \* the shared (double-ended) queue
          rV,     \* per-process return value
          pc      \* per-process program counter

vars == << queue, rV, pc >>

RetVals == Val \cup {null, "ok", "full", "empty"}

-----------------------------------------------------------------------------
(* Operations *)

\* Enqueue: append to the back, prepend to the front, or refuse with "full".
Enqueue(self) ==
    \E v \in Val :
        \/ /\ queue' = Append(queue, v)
           /\ rV' = [rV EXCEPT ![self] = "ok"]
        \/ /\ queue' = <<v>> \o queue
           /\ rV' = [rV EXCEPT ![self] = "ok"]
        \/ /\ queue' = queue
           /\ rV' = [rV EXCEPT ![self] = "full"]

\* Dequeue: remove and return the head or the tail; return "empty" if empty.
Dequeue(self) ==
    IF queue # << >>
       THEN \/ /\ rV' = [rV EXCEPT ![self] = Head(queue)]
               /\ queue' = Tail(queue)
            \/ /\ rV' = [rV EXCEPT ![self] = queue[Len(queue)]]
               /\ queue' = SubSeq(queue, 1, Len(queue) - 1)
       ELSE /\ rV' = [rV EXCEPT ![self] = "empty"]
            /\ queue' = queue

-----------------------------------------------------------------------------
(* Process steps *)

L1(self) ==
    /\ pc[self] = "L1"
    /\ \/ Enqueue(self)
       \/ Dequeue(self)
    /\ pc' = [pc EXCEPT ![self] = "L2"]

L2(self) ==
    /\ pc[self] = "L2"
    /\ rV' = [rV EXCEPT ![self] = null]
    /\ pc' = [pc EXCEPT ![self] = "L1"]
    /\ UNCHANGED queue

proc(self) == L1(self) \/ L2(self)

-----------------------------------------------------------------------------
(* Specification *)

Init ==
    /\ queue = << >>
    /\ rV = [p \in Procs |-> null]
    /\ pc = [p \in Procs |-> "L1"]

Next == \E self \in Procs : proc(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(proc(self))

-----------------------------------------------------------------------------
(* Properties *)

TypeOK ==
    /\ queue \in Seq(Val)
    /\ rV \in [Procs -> RetVals]
    /\ pc \in [Procs -> {"L1", "L2"}]

\* A process at L1 always holds the null return value.
NullAtL1 == \A p \in Procs : pc[p] = "L1" => rV[p] = null

\* Every process makes progress: it completes operations infinitely often.
Progress == \A p \in Procs : []<>(pc[p] = "L2") /\ []<>(pc[p] = "L1")

\* State constraint for bounded model checking (N = 3 in the configuration).
StateConstraint == Len(queue) <= N

=============================================================================