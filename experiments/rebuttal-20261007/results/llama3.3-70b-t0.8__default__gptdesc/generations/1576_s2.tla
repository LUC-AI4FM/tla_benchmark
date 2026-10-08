```
MODULE QueueSystem
EXTENDS Integers, Sequences, TLC

CONSTANTS Procs, Val, N
VARIABLES queue, rV

Init ==
  /\ queue = <<
  /\ rV = [i \in Procs |-> NULL]

Next ==
  (\E i \in Procs :
    \/ (EnqueueFront(i) /\ rV' = [rV EXCEPT ![i] = "okay"])
    \/ (EnqueueBack(i) /\ rV' = [rV EXCEPT ![i] = "okay"])
    \/ (DequeueHead(i) /\ rV' = [rV EXCEPT ![i] = Head(queue)])
    \/ (DequeueTail(i) /\ rV' = [rV EXCEPT ![i] = Last(queue)])
    \/ (AttemptDequeueEmpty(i) /\ rV' = [rV EXCEPT ![i] = "empty"])
  ) /\ queue' = IF EnqueueFront(i) OR EnqueueBack(i)
            THEN IF EnqueueFront(i)
                 THEN Prepend(Val, queue)
                 ELSE Append(queue, Val)
            ELSE IF DequeueHead(i)
                 THEN Tail(queue)
                 ELSE IF DequeueTail(i)
                      THEN SubSeq(queue, 1, Len(queue) - 1)
                      ELSE queue
  /\ UNCHANGED <<Procs, Val, N>>

EnqueueFront(i) ==
  Len(queue) < N

EnqueueBack(i) ==
  Len(queue) < N

DequeueHead(i) ==
  queue # <<

DequeueTail(i) ==
  queue # <<

AttemptDequeueEmpty(i) ==
  queue = <<

P(self) ==
  /\ EnqueueFront(self)
  \/ EnqueueBack(self)
  \/ DequeueHead(self)
  \/ DequeueTail(self)
  \/ AttemptDequeueEmpty(self)

Spec ==
  Init /\ [][Next]_<<queue, rV>>
  /\ WF_vars(<<queue, rV>>, P(self)) (self \in Procs)
  /\ []Len(queue) <= N

THEOREM Spec => []<>[] queue # <<
```