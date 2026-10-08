---- MODULE DijkstraTokenRing ----
EXTENDS Naturals

CONSTANTS N, K

ASSUME
  /\ N \in Nat
  /\ N > 0
  /\ K \in Nat
  /\ K > N

VARIABLES val

vars == << val >>

Proc == 0..(N - 1)

IncK(x) == IF x = K - 1 THEN 0 ELSE x + 1

TypeOK == val \in [Proc -> 0..(K - 1)]

Init == TypeOK

HoldsAt(i, v) ==
  IF i = 0
    THEN v[0] = v[N - 1]
    ELSE v[i] # v[i - 1]

Holds(i) == HoldsAt(i, val)

Step(i) ==
  IF i = 0 THEN
    /\ val[0] = val[N - 1]
    /\ val' = [val EXCEPT ![0] = IncK(@)]
  ELSE
    /\ i \in 1..(N - 1)
    /\ val[i] # val[i - 1]
    /\ val' = [val EXCEPT ![i] = val[i - 1]]

Next == \E i \in Proc : Step(i)

Fairness == \A i \in Proc : WF_vars(Step(i))

Spec == Init /\ [][Next]_vars /\ Fairness

AtLeastOneHolds == \E i \in Proc : Holds(i)

ExactlyOneHolds ==
  \E i \in Proc :
    /\ Holds(i)
    /\ \A j \in Proc : Holds(j) => j = i

Safety == [] AtLeastOneHolds

Liveness == <>[] ExactlyOneHolds

====