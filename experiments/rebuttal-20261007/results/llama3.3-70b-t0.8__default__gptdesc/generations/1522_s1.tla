```tla
MODULE HuangTerminationDetection

EXTENDS Integers, FiniteSets, Reals

CONSTANTS Procs, Leader
VARIABLES active, weight, queue, terminated

Init ==
  /\ active = [p \in Procs |-> TRUE]
  /\ weight = [p \in Procs |-> 1/Cardinality(Procs)]
  /\ queue = [p \in Procs |-> <<>>]
  /\ terminated = FALSE

TypeInvariant ==
  /\ active \in [Procs -> BOOLEAN]
  /\ weight \in [Procs -> DyadicRational]
  /\ queue \in [Procs -> Seq(Message)]
  /\ terminated \in BOOLEAN

WeightSumInv ==
  LET sum_weights == +[weight[p] | p \in Procs]
      sum_queue == +[1/2 |<<m>> \in UNION {queue[p] : p \in Procs}]
  IN
    sum_weights + sum_queue = 1

TerminationDetectedInv ==
  terminated =>
    (\A p \in Procs : ~active[p]) /\ (\A p \in Procs : queue[p] = <<>>)

Send(p, q) ==
  /\ active[p]
  /\ weight[p] > 0
  /\ queue' = [queue EXCEPT ![q] = Append(queue[q], weight[p]/2)]
  /\ weight' = [weight EXCEPT ![p] = weight[p]/2]
  /\ active' = active
  /\ terminated' = terminated

Receive(p, q) ==
  /\ ~active[p]
  /\ queue[p] # <<>>
  /\ queue' = [queue EXCEPT ![p] = Tail(queue[p])]
  /\ weight' = [weight EXCEPT ![p] = weight[p] + Head(queue[p])/2]
  /\ active' = [active EXCEPT ![p] = TRUE]
  /\ terminated' = terminated

Idle(p) ==
  /\ ~active[p]
  /\ queue' = queue
  /\ weight' = weight
  /\ active' = active
  /\ terminated' = terminated

LeaderDetectTermination ==
  /\ active[Leader]
  /\ weight[Leader] = 1/2
  /\ (\A p \in Procs : ~active[p])
  /\ (\A p \in Procs : queue[p] = <<>>)
  /\ terminated' = TRUE
  /\ queue' = queue
  /\ weight' = weight
  /\ active' = active

Next ==
  \/ (\E p, q \in Procs : Send(p, q))
  \/ (\E p, q \in Procs : Receive(p, q))
  \/ (\E p \in Procs : Idle(p))
  \/ LeaderDetectTermination

Spec ==
  /\ Init
  /\ [][Next]_<<active, weight, queue, terminated>>
  /\ WF_Vars(Next)

THEOREM Spec => []WeightSumInv
THEOREM Spec => []TypeInvariant
THEOREM Spec => []TerminationDetectedInv
THEOREM Spec => <><terminated

DyadicRational == {x \in Reals : x = p/q, p, q \in Integers, q # 0}
Message == [weight |-> DyadicRational]

=============================================================================
```