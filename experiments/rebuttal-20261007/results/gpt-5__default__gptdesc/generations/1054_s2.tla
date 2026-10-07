------------------------------ MODULE DijkstraTokenRing ------------------------------

EXTENDS Naturals, Integers

CONSTANTS N, M

ASSUME /\ N \in Nat /\ N >= 1
       /\ M \in Nat /\ M >= 1
       /\ N <= M + 1

VARIABLES x

Val  == 0 .. (M - 1)
Node == 0 .. (N - 1)

TypeOK == x \in [Node -> Val]

TokenAt(i) ==
  IF i = 0
    THEN x[0] = x[N - 1]
    ELSE x[i] /= x[i - 1]

UniqueToken ==
  \E i \in Node:
    /\ TokenAt(i)
    /\ \A j \in Node: j /= i => ~TokenAt(j)

Init ==
  x \in [Node -> Val]

Proc(i) ==
  IF i = 0 THEN
    /\ x[0] = x[N - 1]
    /\ x' = [x EXCEPT ![0] = (x[0] + 1) % M]
  ELSE
    /\ x[i] /= x[i - 1]
    /\ x' = [x EXCEPT ![i] = x[i - 1]]

Next ==
  \E i \in Node: Proc(i)

vars == << x >>

Fairness ==
  \A i \in Node: WF_vars(Proc(i))

Spec ==
  Init /\ [][Next]_vars /\ Fairness

Stabilization ==
  <>[] UniqueToken

SafetyInvariant ==
  []TypeOK

THEOREM Spec => SafetyInvariant

THEOREM Spec => Stabilization

=============================================================================