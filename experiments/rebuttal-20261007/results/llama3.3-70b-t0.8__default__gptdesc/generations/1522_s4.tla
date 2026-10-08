```
MODULE HuangTerminationDetection
EXTENDS Integers, Reals, Sequences

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
  /\ active' = active
  /\ terminated' = terminated

Idle(p) ==
  /\ p \in Procs
  /\ active[p] = TRUE
  /\ weight[p] = 0
  /\ queue[p] = <<>>
  /\ active' = [active EXCEPT ![p] = FALSE]
  /\ weight' = weight
  /\ queue' = queue
  /\ terminated' = terminated

Next ==
  \/ \E p, q \in Procs : Send(p, q)
  \/ \E p, q \in Procs : Receive(p, q)
  \/ \E p \in Procs : Idle(p)

Spec == Init /\ [][Next]_<<active, weight, queue, terminated>>

THEOREM Spec => []TerminationDetected
THEOREM Spec => <>TerminationDetected

TerminationDetected ==
  /\ \A p \in Procs : ~active[p]
  /\ \A p \in Procs : weight[p] = 0
  /\ \A p \in Procs : queue[p] = <<>>
  /\ terminated = TRUE

WF_Send(p, q) == WF-vars(Next, Send(p, q), <<active, weight, queue, terminated>>)
SF_Send(p, q) == SF-vars(Next, Send(p, q), <<active, weight, queue, terminated>>)

WF_Receive(p, q) == WF-vars(Next, Receive(p, q), <<active, weight, queue, terminated>>)
SF_Receive(p, q) == SF-vars(Next, Receive(p, q), <<active, weight, queue, terminated>>)

WF_Idle(p) == WF-vars(Next, Idle(p), <<active, weight, queue, terminated>>)
SF_Idle(p) == SF-vars(Next, Idle(p), <<active, weight, queue, terminated>>)

Fairness ==
  /\ \A p, q \in Procs : WF_Send(p, q) /\ SF_Send(p, q)
  /\ \A p, q \in Procs : WF_Receive(p, q) /\ SF_Receive(p, q)
  /\ \A p \in Procs : WF_Idle(p) /\ SF_Idle(p)

```
Note: `WF-vars` and `SF-vars` are not built-in TLA+ operators. To define weak and strong fairness conditions in TLA+, you would typically use the `WF` and `SF` operators, along with action definitions that capture the enabledness of actions. For example:
```
WF_Send(p, q) == WF(Next, Send(p, q))
SF_Send(p, q) == SF(Next, Send(p, q))
```