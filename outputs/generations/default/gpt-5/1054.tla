---- MODULE DijkstraTokenRing ----
EXTENDS Naturals

CONSTANTS N, M

ASSUME N \in Nat /\ N >= 1 /\ M \in Nat /\ M >= 1 /\ N <= M + 1

VARIABLES x

Nodes == 0..(N - 1)
Values == 0..(M - 1)

Pred(i) == IF i = 0 THEN N - 1 ELSE i - 1
Inc(v) == IF v = M - 1 THEN 0 ELSE v + 1

TypeOK == x \in [Nodes -> Values]

Enabled(i) ==
  IF i = 0
  THEN x[0] = x[N - 1]
  ELSE x[i] # x[Pred(i)]

Init == TypeOK

Act(i) ==
  IF i = 0 THEN
    /\ x[0] = x[N - 1]
    /\ x' = [x EXCEPT ![0] = Inc(@)]
  ELSE
    /\ x[i] # x[Pred(i)]
    /\ x' = [x EXCEPT ![i] = x[Pred(i)]]

Next == \E i \in Nodes: Act(i)

Spec == Init /\ [][Next]_x /\ \A i \in Nodes: WF_x(Act(i))

UniqueToken ==
  \E i \in Nodes:
    Enabled(i) /\ \A j \in Nodes: j # i => ~Enabled(j)

Stabilizes == <>[]UniqueToken

THEOREM Spec => []TypeOK
THEOREM Spec => Stabilizes
====