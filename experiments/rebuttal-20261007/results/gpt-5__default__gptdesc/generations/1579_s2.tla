----------------------------- MODULE DijkstraTokenRing -----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS N, K

ASSUME N \in Nat /\ N > 0 /\ K \in Nat /\ K > N

VARIABLES v

Indices == 0..(N - 1)
Values  == 0..(K - 1)

TypeOK == v \in [Indices -> Values]

Pred(i) == IF i = 0 THEN N - 1 ELSE i - 1

TokenHolder(i) ==
  i \in Indices /\
  IF i = 0
    THEN v[i] = v[Pred(i)]
    ELSE v[i] # v[Pred(i)]

TokenHolders == { i \in Indices : TokenHolder(i) }

SomeToken   == Cardinality(TokenHolders) >= 1
SingleToken == Cardinality(TokenHolders) = 1

Init == TypeOK

Step(i) ==
  i \in Indices /\
  IF i = 0 THEN
    /\ v[i] = v[Pred(i)]
    /\ v' = [v EXCEPT ![i] = (v[i] + 1) mod K]
  ELSE
    /\ v[i] # v[Pred(i)]
    /\ v' = [v EXCEPT ![i] = v[Pred(i)]]

Next == \E i \in Indices: Step(i)

Fairness == \A i \in Indices: WF_v(Step(i))

Spec == Init /\ [][Next]_v /\ Fairness

THEOREM TypeInvariant == Spec => []TypeOK

THEOREM AlwaysSomeToken == Spec => []SomeToken

THEOREM Convergence == Spec => <>[]SingleToken

====================================================================================