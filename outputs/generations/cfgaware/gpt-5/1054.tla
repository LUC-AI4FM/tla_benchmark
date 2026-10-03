---- MODULE DijkstraTokenRing ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M

ASSUME
  /\ N \in Nat
  /\ N >= 1
  /\ M \in Nat
  /\ M >= 1
  /\ N <= M + 1

VARIABLES x

Node == 0..(N - 1)
Val  == 0..(M - 1)

Prev(i) == IF i = 0 THEN N - 1 ELSE i - 1
Inc(v)  == IF v = M - 1 THEN 0 ELSE v + 1

TypeOK == x \in [Node -> Val]

Init == x \in [Node -> Val]

Node0Step ==
  /\ x[0] = x[Prev(0)]
  /\ x' = [x EXCEPT ![0] = Inc(@)]

NodeiStep(i) ==
  /\ i \in Node \ {0}
  /\ x[i] # x[Prev(i)]
  /\ x' = [x EXCEPT ![i] = x[Prev(i)]]

Next ==
  \/ Node0Step
  \/ \E i \in Node \ {0} : NodeiStep(i)

TokAt(i) == x[i] # x[Prev(i)]
TokCount == Cardinality({ i \in Node : TokAt(i) })
UniqueToken == TokCount = 1

Spec ==
  /\ Init
  /\ [][Next]_x
  /\ WF_x(Node0Step)
  /\ \A i \in Node \ {0} : WF_x(NodeiStep(i))

Stabilized == <>[] UniqueToken

====