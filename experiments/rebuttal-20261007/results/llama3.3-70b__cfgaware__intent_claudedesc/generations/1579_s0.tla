---------------------------- MODULE DijkstraTokenRing ----------------------------
EXTENDS Integers

CONSTANT N, K
VARIABLE values

SomeoneHoldsToken == \E i \in 0..N-1 : 
  (i = 0 /\ values[0] = values[(N-1)]) \/ 
  (i # 0 /\ values[i] # values[(i-1) % N])

EventuallyJustOneHoldsToken == <>(\E i \in 0..N-1 : 
  (\A j \in 0..N-1 : (j = i) <=> 
    ((j = 0 /\ values[0] = values[(N-1)]) \/ 
     (j # 0 /\ values[j] # values[(j-1) % N]))))

Spec == 
  /\ values \in [0..N-1 -> 0..K-1]
  /\ [](SomeoneHoldsToken)
  /\ WF_vars({<<i|->values[i] : i \in 0..N-1>>}, {<<i|->values[i] : i \in 0..N-1>>})
  /\ [](EventuallyJustOneHoldsToken => EventuallyJustOneHoldsToken)

THEOREM Spec => []SomeoneHoldsToken
THEOREM Spec => EventuallyJustOneHoldsToken

=============================================================================