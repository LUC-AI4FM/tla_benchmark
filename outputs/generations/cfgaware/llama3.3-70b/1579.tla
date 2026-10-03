---------------------------- MODULE DijkstraTokenRing ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N, K
VARIABLE values

SomeoneHoldsToken == \E i \in 0..N-1 : values[i] = values[(i + 1) % N]
EventuallyJustOneHoldsToken == <>[]~(SomeoneHoldsToken /\ \A i \in 0..N-1 : values[i] # values[(i + 1) % N])

Spec ==
  /\ values \in [0..N-1 -> 0..K-1]
  /\ WF_vars({values}, {i \in 0..N-1 : values[i] = values[(i + 1) % N]})
  /\ []<>(\E i \in 0..N-1 :
      IF i = 0
      THEN values' = [values EXCEPT ![i] = (values[i] + 1) % K]
      ELSE values' = [values EXCEPT ![i] = values[(i - 1 + N) % N]]
    )

THEOREM Spec => []<>SomeoneHoldsToken
THEOREM Spec => EventuallyJustOneHoldsToken

=============================================================================