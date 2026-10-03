------------------------------ MODULE QueueSpec ------------------------------
EXTENDS Naturals, Sequences, TemporalOperators

CONSTANTS
  Val,
  Procs,
  N

VARIABLES
  queue,
  rV

Init ==
  /\ queue = <<>>
  /\ rV = [i \in Procs |-> "null"]

EnqueueFront(i) ==
  \E v \in Val :
    ((Len(queue) < N
      /\ queue' = v ~ queue
      /\ rV' = [rV EXCEPT ![i] = "okay"])
     \/ (Len(queue) >= N
          /\ rV' = [rV EXCEPT ![i] = "full"]
          /\ queue' = queue))

EnqueueBack(i) ==
  \E v \in Val :
    ((Len(queue) < N
      /\ queue' = queue ~ v
      /\ rV' = [rV EXCEPT ![i] = "okay"])
     \/ (Len(queue) >= N
          /\ rV' = [rV EXCEPT ![i] = "full"]
          /\ queue' = queue))

DequeueHead(i) ==
  ((Len(queue) > 0
    /\ queue' = SubSeq(queue, 2, Len(queue))
    /\ rV' = [rV EXCEPT ![i] = queue[1]])
   \/ (Len(queue) = 0
        /\ rV' = [rV EXCEPT ![i] = "empty"]
        /\ queue' = queue))

DequeueTail(i) ==
  ((Len(queue) > 0
    /\ queue' = SubSeq(queue, 1, Len(queue)-1)
    /\ rV' = [rV EXCEPT ![i] = Last(queue)])
   \/ (Len(queue) = 0
        /\ rV' = [rV EXCEPT ![i] = "empty"]
        /\ queue' = queue))

ProcAction(i) == EnqueueFront(i) \/ EnqueueBack(i) \/ DequeueHead(i) \/ DequeueTail(i)

Stutter ==
  /\ queue' = queue
  /\ rV' = rV

Next ==
  \E i \in Procs : ProcAction(i) \/ Stutter

vars == <<queue, rV>>

Fairness == \A i \in Procs : WF_vars(ProcAction(i))

Spec == Init /\ [][Next]_vars /\ Fairness

=============================================================================