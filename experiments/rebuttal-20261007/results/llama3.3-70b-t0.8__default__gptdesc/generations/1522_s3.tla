```
MODULE HuangTerminationDetection
EXTENDS Integers, FiniteSets, Reals

CONSTANTS Procs, Leader
VARIABLES active, weight, queue, terminated

Init ==
  /\ active \in [Procs -> {True, False}]
  /\ weight \in [Procs -> (0..1)]
  /\ queue \in [Procs -> SUBSET Message]
  /\ terminated = False
  /\ active[Leader] = True
  /\ Sum({weight[p] : p \in Procs}) + Sum({m.weight : m \in Union({queue[p] : p \in Procs})}) = 1

Next ==
  (\E p \in Procs :
    \/ Send(p)
    \/ Receive(p)
    \/ Idle(p))
  /\ terminated' = IF terminated THEN True ELSE /\ \A p \in Procs : ~active[p]

Send(p) ==
  /\ active[p]
  /\ \E m \in Message :
    /\ weight[p] > 0
    /\ queue'[p] = queue[p] \cup {m}
    /\ weight'[p] = weight[p] - m.weight
    /\ m.to \in Procs
    /\ queue'[m.to] = queue[m.to] \cup {m}

Receive(p) ==
  /\ queue[p] # {}
  /\ \E m \in queue[p] :
    /\ queue'[p] = queue[p] \ {m}
    /\ weight'[p] = weight[p] + m.weight
    /\ active'[p] = IF weight[p] + m.weight > 0 THEN True ELSE False

Idle(p) ==
  /\ ~active[p]
  /\ queue'[p] = queue[p]
  /\ weight'[p] = weight[p]

Spec == Init /\ [][Next]_<<active, weight, queue, terminated>>

TerminationDetected == \A p \in Procs : ~active[p] /\ queue[p] = {}

SafetyInvariant ==
  terminated => TerminationDetected

LivenessProperty ==
  <>TerminationDetected

Fairness ==
  WeakFairness(Procs, Send)
  /\ WeakFairness(Procs, Receive)

THEOREM Spec => []SafetyInvariant
THEOREM Spec => LivenessProperty

=============================================================================
```
Note: The above TLA+ specification uses the `Message` type which is not explicitly defined. In a real-world implementation, you would need to define this type as well. Additionally, the `Sum` function used in the `Init` predicate and elsewhere assumes that it can handle sets of numbers; if your version of TLA+ does not support this, you may need to use an explicit fold instead.