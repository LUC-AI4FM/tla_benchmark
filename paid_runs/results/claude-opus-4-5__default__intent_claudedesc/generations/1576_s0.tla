---------------------------- MODULE ConcurrentDeque ----------------------------
EXTENDS Sequences, Integers, FiniteSets

CONSTANTS Values, Procs, N

VARIABLES queue, result

vars == <<queue, result>>

TypeOK ==
    /\ queue \in Seq(Values)
    /\ result \in [Procs -> {"success", "full", "empty", "none"} \cup Values]

StateConstraint == Len(queue) <= N

Init ==
    /\ queue = <<>>
    /\ result = [p \in Procs |-> "none"]

EnqueueBack(p, v) ==
    /\ Len(queue) < N
    /\ queue' = Append(queue, v)
    /\ result' = [result EXCEPT ![p] = "success"]

EnqueueFront(p, v) ==
    /\ Len(queue) < N
    /\ queue' = <<v>> \o queue
    /\ result' = [result EXCEPT ![p] = "success"]

ReportFull(p) ==
    /\ Len(queue) >= N
    /\ queue' = queue
    /\ result' = [result EXCEPT ![p] = "full"]

DequeueFront(p) ==
    /\ Len(queue) > 0
    /\ result' = [result EXCEPT ![p] = Head(queue)]
    /\ queue' = Tail(queue)

DequeueBack(p) ==
    /\ Len(queue) > 0
    /\ result' = [result EXCEPT ![p] = queue[Len(queue)]]
    /\ queue' = SubSeq(queue, 1, Len(queue) - 1)

ReportEmpty(p) ==
    /\ Len(queue) = 0
    /\ queue' = queue
    /\ result' = [result EXCEPT ![p] = "empty"]

ClearResult(p) ==
    /\ result[p] # "none"
    /\ result' = [result EXCEPT ![p] = "none"]
    /\ queue' = queue

ProcessAction(p) ==
    \/ \E v \in Values : EnqueueBack(p, v)
    \/ \E v \in Values : EnqueueFront(p, v)
    \/ ReportFull(p)
    \/ DequeueFront(p)
    \/ DequeueBack(p)
    \/ ReportEmpty(p)
    \/ ClearResult(p)

Next == \E p \in Procs : ProcessAction(p)

Fairness == \A p \in Procs : WF_vars(ProcessAction(p))

Spec == Init /\ [][Next]_vars /\ Fairness

================================================================================