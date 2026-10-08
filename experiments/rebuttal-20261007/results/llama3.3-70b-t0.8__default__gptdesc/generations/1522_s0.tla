```
MODULE HuangTerminationDetection
EXTENDS Integers, FiniteSets, Reals

CONSTANTS Procs, Leader
VARIABLES active, weight, queue, msgInTransit, terminated

Init ==
  /\ active \in [Procs -> {True, False}]
  /\ weight \in [Procs -> (0..1)]
  /\ queue \in [Procs -> {}]
  /\ msgInTransit = {}
  /\ terminated = False
  /\ weight[Leader] = 1
  /\ forall p \in Procs \ {Leader} : weight[p] = 0

Next ==
  \/ Send(p \in Procs)
  \/ Receive(p \in Procs, q \in Procs)
  \/ Idle(p \in Procs)

Send(p) ==
  /\ active[p]
  /\ weight[p] > 0
  /\ queue' = [queue EXCEPT ![p] = {}]
  /\ msgInTransit' = msgInTransit \cup {<<p, q>> : q \in Procs}
  /\ weight' = [weight EXCEPT ![p] = weight[p] / 2]

Receive(p, q) ==
  /\ <<p, q>> \in msgInTransit
  /\ active[q]
  /\ queue' = [queue EXCEPT ![q] = queue[q] \cup {<<p, q>>}]
  /\ msgInTransit' = msgInTransit \ {<<p, q>>}
  /\ weight' = [weight EXCEPT ![q] = weight[q] + (1/2) * (weight[p] / 2)]
  /\ active' = [active EXCEPT ![q] = True]

Idle(p) ==
  /\ ~active[p]
  /\ queue' = queue
  /\ msgInTransit' = msgInTransit
  /\ weight' = weight

Spec == Init /\ [][Next]_<<active, weight, queue, msgInTransit>>

TerminationInvariant == 
  /\ terminated => (forall p \in Procs : ~active[p])
  /\ terminated => (msgInTransit = {})
  /\ SUM({weight[p] : p \in Procs} \cup {1/2 : <<p, q>> \in msgInTransit}) = 1

Fairness == 
  WF_Vars(Next, <<active, weight, queue, msgInTransit>>)
  SF_Vars(Next, <<active, weight, queue, msgInTransit>>)

THEOREM Spec => []TerminationInvariant
THEOREM Spec => <>terminated
```