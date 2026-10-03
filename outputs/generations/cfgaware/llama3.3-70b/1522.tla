---------------------------- MODULE HuangTerminationDetection ----------------------------
EXTENDS Integers, Reals, FiniteSets

CONSTANTS Procs, Leader
VARIABLES active, weight, queue, messagesInTransit, terminated

Init ==
  /\ active = [p \in Procs |-> TRUE]
  /\ weight = [p \in Procs |-> 1 / Cardinality(Procs)]
  /\ queue = [p \in Procs |-> <<>>]
  /\ messagesInTransit = <<>>
  /\ terminated = FALSE

TypeInvariant ==
  /\ active \in [Procs -> BOOLEAN]
  /\ weight \in [Procs -> DyadicRational]
  /\ queue \in [Procs -> Seq(Message)]
  /\ messagesInTransit \in Seq(Message)
  /\ terminated \in BOOLEAN

DyadicRational == {x \in Reals : x = p / (2 ^ n) /\ p \in Integers /\ n \in Nat}

Message == [sender |-> Procs, receiver |-> Procs, weight |-> DyadicRational]

Send(p, q, w) ==
  /\ active[p] = TRUE
  /\ weight[p] >= w
  /\ queue' = [queue EXCEPT ![p] = Append(queue[p], <<[sender |-> p, receiver |-> q, weight |-> w]>>)]
  /\ weight' = [weight EXCEPT ![p] = weight[p] - w]
  /\ messagesInTransit' = Append(messagesInTransit, <<[sender |-> p, receiver |-> q, weight |-> w]>>)
  /\ active' = active
  /\ terminated' = terminated

Receive(p, m) ==
  /\ queue[p] # <<>>
  /\ m = Head(queue[p])
  /\ queue' = [queue EXCEPT ![p] = Tail(queue[p])]
  /\ weight' = [weight EXCEPT ![p] = weight[p] + m.weight]
  /\ messagesInTransit' = Tail(messagesInTransit)
  /\ active' = [active EXCEPT ![p] = weight'[p] > 0]
  /\ terminated' = terminated

Idle(p) ==
  /\ active[p] = TRUE
  /\ weight[p] > 0
  /\ queue' = queue
  /\ weight' = [weight EXCEPT ![p] = weight[p] / 2]
  /\ messagesInTransit' = messagesInTransit
  /\ active' = [active EXCEPT ![p] = weight'[p] > 0]
  /\ terminated' = terminated

Next ==
  \/ \E p, q \in Procs, w \in DyadicRational : Send(p, q, w)
  \/ \E p \in Procs, m \in Message : Receive(p, m)
  \/ \E p \in Procs : Idle(p)

Spec == Init /\ [][Next]_<<active, weight, queue, messagesInTransit, terminated>>

THEOREM Spec => []TerminationDetected
THEOREM Spec => <>TerminationDetected

TerminationDetected ==
  /\ terminated = TRUE
  /\ \A p \in Procs : active[p] = FALSE
  /\ messagesInTransit = <<>>
  /\ queue = [p \in Procs |-> <<>>]

=============================================================================