------------------------------ MODULE DijkstraTokenRing ------------------------------

EXTENDS Naturals

CONSTANTS N, M

ASSUME N \in Nat /\ N >= 1 /\ M \in Nat /\ M >= 1 /\ N <= M + 1

Proc == 0..(N - 1)
Val  == 0..(M - 1)

VARIABLES x

Inc(v) == IF v = M - 1 THEN 0 ELSE v + 1

TypeOK == x \in [Proc -> Val]

Init == TypeOK

Priv(i) ==
  IF i = 0
  THEN x[0] = x[N - 1]
  ELSE x[i] # x[i - 1]

Step(i) ==
  /\ i \in Proc
  /\ IF i = 0
     THEN Priv(0) /\ x' = [x EXCEPT ![0] = Inc(@)]
     ELSE Priv(i) /\ x' = [x EXCEPT ![i] = x[i - 1]]

Next == \E i \in Proc: Step(i)

UniqueToken ==
  \E i \in Proc:
    Priv(i) /\ \A j \in Proc: j # i => ~Priv(j)

Stabilization == <>[] UniqueToken

Spec ==
  /\ Init
  /\ [][Next]_x
  /\ \A i \in Proc: WF_x(Step(i))

=============================================================================