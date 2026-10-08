---------------------------- MODULE ConcurrentQueue ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N, Values, Processes
VARIABLE queue, results, processStates

Init ==
  /\ queue = <<>>
  /\ results = [p \in Processes |-> NULL]
  /\ processStates = [p \in Processes |-> "idle"]

EnqueueBack(v, p) ==
  /\ queue' = Append(queue, v)
  /\ results' = [results EXCEPT ![p] = "success"]
  /\ processStates' = [processStates EXCEPT ![p] = "idle"]
  /\ UNCHANGED << >>

EnqueueFront(v, p) ==
  /\ queue' = Prepend(queue, v)
  /\ results' = [results EXCEPT ![p] = "success"]
  /\ processStates' = [processStates EXCEPT ![p] = "idle"]
  /\ UNCHANGED << >>

ReportFull(p) ==
  /\ queue' = queue
  /\ results' = [results EXCEPT ![p] = "full"]
  /\ processStates' = [processStates EXCEPT ![p] = "idle"]
  /\ Len(queue) = N

DequeueFront(p) ==
  /\ queue' = Tail(queue)
  /\ results' = [results EXCEPT ![p] = Head(queue)]
  /\ processStates' = [processStates EXCEPT ![p] = "idle"]
  /\ queue # << >>

DequeueBack(p) ==
  /\ queue' = SubSeq(queue, 1, Len(queue) - 1)
  /\ results' = [results EXCEPT ![p] = Last(queue)]
  /\ processStates' = [processStates EXCEPT ![p] = "idle"]
  /\ queue # << >>

ReportEmpty(p) ==
  /\ queue' = queue
  /\ results' = [results EXCEPT ![p] = "empty"]
  /\ processStates' = [processStates EXCEPT ![p] = "idle"]
  /\ queue = << >>

Next(p) ==
  \/ \E v \in Values : EnqueueBack(v, p)
  \/ \E v \in Values : EnqueueFront(v, p)
  \/ ReportFull(p)
  \/ DequeueFront(p)
  \/ DequeueBack(p)
  \/ ReportEmpty(p)

Spec ==
  /\ Init
  /\ [][Next(\_p) /\ WF_(Next)(\_p)]_{queue, results, processStates}
  /\ Len(queue) <= N

THEOREM Spec => []Len(queue) <= N
=============================================================================