```
MODULE HuangTerminationDetection
EXTENDS Integers, FiniteSets

CONSTANTS ProcSet, Leader
VARIABLES active, weight, msgQueue

Init ==
  /\ active = {Leader}
  /\ weight = [p \in ProcSet |-> IF p = Leader THEN 1 ELSE 0]
  /\ msgQueue = {}

Next ==
  \/ \E p \in ProcSet, q \in ProcSet:
        /\ p /= q
        /\ p \in active
        /\ weight[p] > 0
        /\ msgQueue' = msgQueue \cup {<<p, q, weight[p] / 2>>}
        /\ weight' = [weight EXCEPT ![p] = weight[p] / 2]
        /\ UNCHANGED active
  \/ \E p \in ProcSet, q \in ProcSet, m \in msgQueue:
        /\ p = m[2]
        /\ q = m[3]
        /\ msgQueue' = msgQueue \ {m}
        /\ weight' = [weight EXCEPT ![q] = weight[q] + m[4]]
        /\ active' = active \cup {q}
        /\ UNCHANGED weight[p]
  \/ \E p \in ProcSet:
        /\ p /= Leader
        /\ p \in active
        /\ weight[p] = 0
        /\ msgQueue' = msgQueue \cup {<<p, Leader, 0>>}
        /\ weight' = [weight EXCEPT ![p] = 0]
        /\ active' = active \ {p}
  \/ Leader \in active
     /\ weight[Leader] = 1
     /\ msgQueue = {}
     /\ weight' = weight
     /\ msgQueue' = msgQueue
     /\ active' = active \ {Leader}
  \/ \E m \in msgQueue:
        /\ m[2] = Leader
        /\ msgQueue' = msgQueue \ {m}
        /\ weight' = [weight EXCEPT ![Leader] = weight[Leader] + m[4]]
        /\ UNCHANGED active

Spec ==
  Init /\ [][Next]_active /\ [][Next]_weight /\ [][Next]_msgQueue

TerminationNeverFalselyDeclared ==
  [](Leader \in active /\ weight[Leader] = 1 /\ msgQueue = {} => [](~\E p \in ProcSet: p /= Leader /\ (p \in active \/ \E m \in msgQueue: m[2] = p))))

TotalWeightInvariant ==
  [](SUM DOMAIN weight : weight[x] + SUM {m[4] : m \in msgQueue} = 1)

THEOREM Spec => []TerminationNeverFalselyDeclared
THEOREM Spec => []TotalWeightInvariant

Fairness ==
  WF_Vars(Next, active) /\ WF_Vars(Next, weight) /\ WF_Vars(Next, msgQueue)

Liveness ==
  <>[](Leader \in active /\ weight[Leader] = 1 /\ msgQueue = {})

THEOREM Spec => Fairness => Liveness
```