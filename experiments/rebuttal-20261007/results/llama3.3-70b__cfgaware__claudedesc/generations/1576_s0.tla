---------------------------- MODULE Deque --------------------------------
EXTENDS Integers, Sequences

CONSTANT Val, Procs, null, N
VARIABLE queue, rV

vars == <<queue, rV>>

Init ==
  /\ queue = <<
  /\ rV = [p \in Procs |-> null]

L1(p) ==
  \/ Enqueue(p)
  \/ Dequeue(p)

Enqueue(p) ==
  \E v \in Val :
    \/ queue' = Append(queue, v)
    \/ queue' = Prepend(queue, v)
    \/ (queue' = queue /\ rV' = [rV EXCEPT ![p] = "full"])

Dequeue(p) ==
  IF queue # <<
  THEN
    \E v \in {queue[1], Last(queue)} :
      \/ (queue' = Tail(queue) /\ rV' = [rV EXCEPT ![p] = v])
      \/ (queue' = SubSeq(queue, 2, Len(queue)) /\ rV' = [rV EXCEPT ![p] = v])
  ELSE
    (queue' = queue /\ rV' = [rV EXCEPT ![p] = "empty"])

L2(p) ==
  queue' = queue
  /\ rV' = [rV EXCEPT ![p] = null]

Next(p) == L1(p) \/ L2(p)

Spec == Init /\ [][\A p \in Procs : Next(p)]_vars
        /\ WF_vars(\A p \in Procs : Next(p))

THEOREM Spec => []~(queue # << /\ \A p \in Procs : rV[p] = null)
=============================================================================