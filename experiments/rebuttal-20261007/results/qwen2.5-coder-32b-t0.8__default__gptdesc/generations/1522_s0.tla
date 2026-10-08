```tla
MODULE HuangsTerminationDetection

EXTENDS Naturals, Reals, FiniteSets, Sequences

CONSTANTS Procs, Leader

VARIABLES active, weight, messages

Init == 
  /\ active = [p \in Procs |-> TRUE]
  /\ (\E p \in Procs : p = Leader)
  /\ weight = [p \in Procs |-> 1 / Cardinality(Procs)]
  /\ messages = [p \in Procs |-> <<>>]

Send(p, q) ==
  /\ active[p] 
  /\ weight[q] > 0
  /\ \/ q = Leader 
     \/ (\E r \in DOMAIN weight : r # p /\ r # q /\ weight[r] > 0)
  /\ LET halfWeight == weight[p] / 2 IN
    \/ /\ q = Leader
       /\ active' = [active EXCEPT ![p] = FALSE]
       /\ weight' = [weight EXCEPT ![p] = 0, ![Leader] = weight[Leader] + halfWeight]
       /\ messages' = [messages EXCEPT ![q] = Append(messages[q], <<p, halfWeight>>)]
    \/ /\ q # Leader
       /\ active' = active
       /\ weight' = [weight EXCEPT ![p] = halfWeight, ![q] = weight[q] + halfWeight]
       /\ messages' = [messages EXCEPT ![q] = Append(messages[q], <<p, halfWeight>>)]

Receive(p) ==
  /\ active[p]
  /\ Len(messages[p]) > 0
  /\ LET msg == Head(messages[p])
     w == tlstl(msg)
     q == fstt(msg) IN
    /\ active' = active
    /\ weight' = [weight EXCEPT ![p] = weight[p] + w]
    /\ messages' = [messages EXCEPT ![p] = Tail(messages[p])]

Idle ==
  /\ \A p \in Procs : ~active[p]
  /\ \A q \in Procs : Len(messages[q]) = 0

Next == 
  \/ (\E p, q \in Procs : Send(p, q))
  \/ (\E p \in Procs : Receive(p))
  \/ Idle

Spec == 
  /\ Init
  /\ [][Next]_<<active, weight, messages>>
  /\ <>(\A p \in Procs : ~active[p]) 

WF_SendReceive ==
  WF_next(<<active, weight, messages>>, Send)
  /\ WF_next(<<active, weight, messages>>, Receive)

TerminationDetected ==
  (\A p \in Procs : ~active[p])
  /\ (\A q \in Procs : Len(messages[q]) = 0)

SafetyInvariant ==
  \/ ~(\E p \in Procs : active[p] /\ weight[p] <= 0)
  \/ TerminationDetected

LivenessProperty ==
  [](TerminationDetected => []TerminationDetected)

SpecWithFairness ==
  Spec
  /\ WF_SendReceive
  /\ SafetyInvariant
  /\ LivenessProperty
```