---------------------------- MODULE DequeueQueue ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Val,    \* set of values that can be enqueued
          Procs,  \* set of concurrent processes
          N,      \* bound on queue length for model checking
          null    \* "no result" marker

VARIABLES queue,   \* the shared double-ended queue
          results  \* results[p]: result of p's last operation, or null

vars == <<queue, results>>

TypeOK ==
    /\ queue \in Seq(Val)
    /\ results \in [Procs -> Val \cup {"ok", "full", "empty", null}]

Init ==
    /\ queue = <<>>
    /\ results = [p \in Procs |-> null]

\* Enqueue a chosen value at the back
EnqBack(p) ==
    /\ results[p] = null
    /\ \E v \in Val :
         /\ queue' = Append(queue, v)
         /\ results' = [results EXCEPT ![p] = "ok"]

\* Enqueue a chosen value at the front
EnqFront(p) ==
    /\ results[p] = null
    /\ \E v \in Val :
         /\ queue' = <<v>> \o queue
         /\ results' = [results EXCEPT ![p] = "ok"]

\* Report the queue as full, without modifying it
ReportFull(p) ==
    /\ results[p] = null
    /\ results' = [results EXCEPT ![p] = "full"]
    /\ UNCHANGED queue

\* Dequeue from the front
DeqFront(p) ==
    /\ results[p] = null
    /\ queue # <<>>
    /\ results' = [results EXCEPT ![p] = Head(queue)]
    /\ queue' = Tail(queue)

\* Dequeue from the back
DeqBack(p) ==
    /\ results[p] = null
    /\ queue # <<>>
    /\ results' = [results EXCEPT ![p] = queue[Len(queue)]]
    /\ queue' = SubSeq(queue, 1, Len(queue) - 1)

\* Report the queue as empty when no elements are present
ReportEmpty(p) ==
    /\ results[p] = null
    /\ queue = <<>>
    /\ results' = [results EXCEPT ![p] = "empty"]
    /\ UNCHANGED queue

\* Clear the visible result
ClearResult(p) ==
    /\ results[p] # null
    /\ results' = [results EXCEPT ![p] = null]
    /\ UNCHANGED queue

ProcNext(p) ==
    \/ EnqBack(p)
    \/ EnqFront(p)
    \/ ReportFull(p)
    \/ DeqFront(p)
    \/ DeqBack(p)
    \/ ReportEmpty(p)
    \/ ClearResult(p)

Next == \E p \in Procs : ProcNext(p)

Spec == Init /\ [][Next]_vars /\ \A p \in Procs : WF_vars(ProcNext(p))

Constraint == Len(queue) <= N

=============================================================================