------------------------------ MODULE DijkstraTokenRing ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS N, M

ASSUME N \in Nat \ {0} /\ M \in Nat \ {0} /\ N <= M + 1

VARIABLES val

NodeSet == 0..(N - 1)
ValueSet == 0..(M - 1)

TypeOK == val \in [NodeSet -> ValueSet]

Succ(x) == IF x = M - 1 THEN 0 ELSE x + 1

Init == TypeOK

Step0 ==
  /\ val[0] = val[N - 1]
  /\ val' = [val EXCEPT ![0] = Succ(@)]

Step(i) ==
  /\ i \in 1..(N - 1)
  /\ val[i] # val[i - 1]
  /\ val' = [val EXCEPT ![i] = val[i - 1]]

Next ==
  Step0 \/ (\E i \in 1..(N - 1): Step(i))

Tokens ==
  { i \in NodeSet :
      IF i = 0
      THEN val[0] = val[N - 1]
      ELSE val[i] # val[i - 1]
  }

UniqueToken == Cardinality(Tokens) = 1

Fairness ==
  /\ WF_val(Step0)
  /\ \A i \in 1..(N - 1): WF_val(Step(i))

Spec == Init /\ [][Next]_val /\ Fairness

Stabilization == <>[] UniqueToken

THEOREM Spec => []TypeOK
THEOREM Spec => Stabilization

=============================================================================