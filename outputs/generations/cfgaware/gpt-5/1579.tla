------------------------------ MODULE DijkstraTokenRing ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS N, K

ASSUME /\ N \in Nat /\ N > 0
       /\ K \in Nat /\ K > N

VARIABLE v

Proc == 0..(N-1)

Init == v \in [Proc -> 0..(K-1)]

P0 ==
  /\ v[0] = v[N-1]
  /\ v' = [v EXCEPT ![0] = (v[0] + 1) % K]

Pi(i) ==
  /\ i \in 1..(N-1)
  /\ v[i] # v[i-1]
  /\ v' = [v EXCEPT ![i] = v[i-1]]

Next == P0 \/ (\E i \in 1..(N-1): Pi(i))

Fairness == WF_v(P0) /\ \A i \in 1..(N-1): WF_v(Pi(i))

Spec == Init /\ [][Next]_v /\ Fairness

Token(i) == IF i = 0 THEN v[0] = v[N-1] ELSE v[i] # v[i-1]

TokenSet == { i \in Proc : Token(i) }

SomeoneHoldsToken == \E i \in Proc: Token(i)

EventuallyJustOneHoldsToken == <>[](Cardinality(TokenSet) = 1)

THEOREM Spec => [](SomeoneHoldsToken)

THEOREM Spec => EventuallyJustOneHoldsToken

=============================================================================