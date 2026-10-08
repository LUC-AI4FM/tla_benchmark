MODULE DijkstraTokenRing
EXTENDS Naturals

CONSTANTS N, M

VARIABLES X

Domain   == 0..M-1
NodeSet  == 0..N-1

inc(v)   == (v + 1) % M

Pred(i)  == IF i = 0 THEN N - 1 ELSE i - 1

Token(i) == X[i] #= X[Pred(i)]

UniqueTokenInvariant ==
  \E i \in NodeSet :
    /\ Token(i)
    /\ \A j \in NodeSet : (j /= i) => ~Token(j)

Init ==
  /\ X \in [NodeSet -> Domain]

Next ==
  \/ (* node 0 updates *)
     X' = [X EXCEPT ![0] = inc(X[N-1])]
  \/ \E i \in NodeSet :
       i #= 0
       /\ X[i] #= X[Pred(i)]
       /\ X' = [X EXCEPT ![i] = X[Pred(i)]]

Spec ==
  /\ N >= 1
  /\ M >= 1
  /\ N <= M + 1
  /\ Init
  /\ [][Next]_X

EventuallyUniqueToken == <> ([] UniqueTokenInvariant)