```
MODULE DijkstraTokenRing
EXTENDS Integers, FiniteSets

CONSTANTS N, K
ASSUME N > 0, K > N

VARIABLES values

Init ==
  /\ values \in [1..N -> 0..(K-1)]
  /\ \E i \in 1..N : values[i] = 0

Next ==
  /\ \E i \in 1..N :
      IF i = 1 THEN
        IF values[N] = values[1] THEN
          values' = [values EXCEPT ![1] = (values[1] + 1) % K]
        ELSE
          values' = values
      ELSE
        IF values[i-1] # values[i] THEN
          values' = [values EXCEPT ![i] = values[i-1]]
        ELSE
          values' = values

Spec ==
  /\ Init
  /\ [][Next]_values
  /\ WF_vars(Next, values)

TokenHolder(i) == values[i] = 0

AlwaysHasToken ==
  \A t : \E i \in 1..N : TokenHolder(i) @ t

EventuallyOneToken ==
  <>(\A i, j \in 1..N : (TokenHolder(i)) /\ (TokenHolder(j)) => i = j)

THEOREM Spec => AlwaysHasToken
THEOREM Spec => EventuallyOneToken
```