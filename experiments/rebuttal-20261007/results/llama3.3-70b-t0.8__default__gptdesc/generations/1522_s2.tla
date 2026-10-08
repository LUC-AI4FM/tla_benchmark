```
MODULE HuangTerminationDetection
EXTENDS Integers, Reals, Sequences

CONSTANTS Procs, Leader
VARIABLES active, weight, queue, delivered, terminated

Init ==
  /\ active = [p \in Procs |-> TRUE]
  /\ weight = [p \in Procs |-> 1/Cardinality(Procs)]
  /\ queue = [p \in Procs |-> <<>>]
  /\ delivered = FALSE
  /\ terminated = FALSE

Send(p, q) ==
  /\ p \in Procs
  /\ q \in Procs
  /\ active[p] = TRUE
  /\ weight[p] > 0
  /\ queue' = [queue EXCEPT ![p] = Append(queue[p], weight[p]/2)]
  /\ weight' = [weight EXCEPT ![p] = weight[p]/2]
  /\ UNCHANGED <<active, delivered, terminated>>

Receive(p, q) ==
  /\ p \in Procs
  /\ q \in Procs
  /\ queue[q] # <<>>
  /\ active[q] = TRUE
  /\ weight' = [weight EXCEPT ![q] = weight[q] + Head(queue[q])]
  /\ queue' = [queue EXCEPT ![q] = Tail(queue[q])]
  /\ UNCHANGED <<active, delivered, terminated>>

Idle(p) ==
  /\ p \in Procs
  /\ active[p] = TRUE
  /\ weight[p] = 0
  /\ queue[p] = <<>>
  /\ active' = [active EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<weight, queue, delivered, terminated>>

Deliver ==
  /\ ~delivered
  /\ delivered' = TRUE
  /\ UNCHANGED <<active, weight, queue, terminated>>

DetectTermination ==
  /\ terminated' = TRUE
  /\ Forall (p \in Procs, active[p] = FALSE)
  /\ Forall (p \in Procs, queue[p] = <<>>)
  /\ delivered = TRUE
  /\ UNCHANGED <<active, weight, queue, delivered>>

Next ==
  \/ (\E p \in Procs : \E q \in Procs : Send(p, q))
  \/ (\E p \in Procs : \E q \in Procs : Receive(p, q))
  \/ (\E p \in Procs : Idle(p))
  \/ Deliver
  \/ DetectTermination

Spec ==
  /\ Init
  /\ [][Next]_<<active, weight, queue, delivered, terminated>>
  /\ WF_Vars(Next, <<active, weight, queue, delivered, terminated>>)

THEOREM Spec => []Terminated =>
  (\A p \in Procs : active[p] = FALSE) /\
  (\A p \in Procs : queue[p] = <<>>) /\
  delivered

THEOREM Spec => <>(\A p \in Procs : weight[p] = 0 /\ queue[p] = <<>>) => <>Terminated
```