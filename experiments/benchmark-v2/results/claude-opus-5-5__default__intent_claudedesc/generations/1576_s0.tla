---------------------------- MODULE ConcurrentDeque ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Values,   \* the fixed set of values that can be enqueued
          Procs,    \* the set of concurrent processes
          N         \* bound on queue length (used by the state constraint)

ASSUME /\ N \in Nat
       /\ Procs # {}

VARIABLES queue,    \* the shared double-ended queue
          result    \* result[p]: the result of p's last operation, or NoResult

vars == <<queue, result>>

NoResult == "none"
Success  == "ok"
Full     == "full"
Empty    == "empty"

ResultValues == {NoResult, Success, Full, Empty} \cup Values

TypeOK ==
    /\ queue \in Seq(Values)
    /\ result \in [Procs -> ResultValues]

Init ==
    /\ queue = << >>
    /\ result = [p \in Procs |-> NoResult]

\* Enqueue a value at the back of the queue
EnqBack(p) ==
    /\ result[p] = NoResult
    /\ \E v \in Values :
         /\ queue' = Append(queue, v)
         /\ result' = [result EXCEPT ![p] = Success]

\* Enqueue a value at the front of the queue
EnqFront(p) ==
    /\ result[p] = NoResult
    /\ \E v \in Values :
         /\ queue' = <<v>> \o queue
         /\ result' = [result EXCEPT ![p] = Success]

\* Report the queue as full without modifying it (nondeterministic)
ReportFull(p) ==
    /\ result[p] = NoResult
    /\ result' = [result EXCEPT ![p] = Full]
    /\ UNCHANGED queue

\* Dequeue from the front of the queue
DeqFront(p) ==
    /\ result[p] = NoResult
    /\ queue # << >>
    /\ result' = [result EXCEPT ![p] = Head(queue)]
    /\ queue' = Tail(queue)

\* Dequeue from the back of the queue
DeqBack(p) ==
    /\ result[p] = NoResult
    /\ queue # << >>
    /\ result' = [result EXCEPT ![p] = queue[Len(queue)]]
    /\ queue' = SubSeq(queue, 1, Len(queue) - 1)

\* Report the queue as empty when no elements are present
ReportEmpty(p) ==
    /\ result[p] = NoResult
    /\ queue = << >>
    /\ result' = [result EXCEPT ![p] = Empty]
    /\ UNCHANGED queue

\* The result is visible briefly, then cleared
ClearResult(p) ==
    /\ result[p] # NoResult
    /\ result' = [result EXCEPT ![p] = NoResult]
    /\ UNCHANGED queue

Proc(p) ==
    \/ EnqBack(p)
    \/ EnqFront(p)
    \/ ReportFull(p)
    \/ DeqFront(p)
    \/ DeqBack(p)
    \/ ReportEmpty(p)
    \/ ClearResult(p)

Next == \E p \in Procs : Proc(p)

Fairness == \A p \in Procs : WF_vars(Proc(p))

Spec == Init /\ [][Next]_vars /\ Fairness

\* State constraint bounding the queue length for model checking
StateConstraint == Len(queue) <= N

=============================================================================