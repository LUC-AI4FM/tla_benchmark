```
MODULE HuangTerminationDetection
EXTENDS Integers, FiniteSets, Reals

CONSTANTS Procs, Leader
VARIABLES active, weight, queue, terminated

Init ==
  /\ active = [p \in Procs |-> TRUE]
  /\ weight = [p \in Procs |-> 1/Cardinality(Procs)]
  /\ queue = [p \in Procs |-> <<>>]
  /\ terminated = FALSE

Send(p, q) ==
  /\ p \in Procs
  /\ q \in Procs
  /\ active[p] = TRUE
  /\ weight[p] > 0
  /\ queue' = [queue EXCEPT ![p] = Append(queue[p], <<weight[p]/2>>)]
  /\ weight' = [weight EXCEPT ![p] = weight[p]/2]
  /\ active' = active
  /\ terminated' = terminated

Receive(p, q) ==
  /\ p \in Procs
  /\ q \in Procs
  /\ queue[q] # <<>>
  /\ weight' = [weight EXCEPT ![q] = weight[q] + Head(queue[q])]
  /\ queue' = [queue EXCEPT ![q] = Tail(queue[q])]
  /\ active' = [active EXCEPT ![q] = weight'[q] > 0]
  /\ terminated' = terminated

Idle(p) ==
  /\ p \in Procs
  /\ active[p] = TRUE
  /\ weight[p] = 0
  /\ queue[p] = <<>>
  /\ active' = [active EXCEPT ![p] = FALSE]
  /\ weight' = weight
  /\ queue' = queue
  /\ terminated' = (terminated = TRUE) \/ (Procs = {Leader} /\ active[Leader] = FALSE)

Next ==
  \/ \E p, q \in Procs : Send(p, q)
  \/ \E p, q \in Procs : Receive(p, q)
  \/ \E p \in Procs : Idle(p)

Spec ==
  Init /\ [][Next]_<<active, weight, queue, terminated>>
  /\ WF_<<active, weight, queue, terminated>>(Send)
  /\ WF_<<active, weight, queue, terminated>>(Receive)
  /\ SF_<<active, weight, queue, terminated>>(Idle)

THEOREM Spec => []<>(terminated = TRUE)
THEOREM Spec => terminated => []<>(\A p \in Procs : ~active[p])
THEOREM Spec => terminated => []<>(\A p \in Procs : queue[p] = <<>>)
```