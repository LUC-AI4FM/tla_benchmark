```
MODULE DijkstraTokenRing
EXTENDS Integers, FiniteSets

CONSTANTS N, K
ASSUME N > 0 & K > N

VARIABLES values, tokenHolder

Init ==
  /\ values \in [1..N -> 0..(K-1)]
  /\ tokenHolder = {}

Next ==
  \/ \E i \in 1..N :
      IF i = 1
      THEN
        IF values[i] = values[N]
        THEN
          values' = [values EXCEPT ![i] = (values[i] + 1) % K]
          /\ tokenHolder' = IF {i} \in tokenHolder THEN tokenHolder ELSE {i}
        ELSE
          values' = values
          /\ tokenHolder' = tokenHolder
      ELSE
        IF values[i] # values[(i-1)]
        THEN
          values' = [values EXCEPT ![i] = values[(i-1)]]
          /\ tokenHolder' = IF {i} \in tokenHolder THEN tokenHolder ELSE {}
        ELSE
          values' = values
          /\ tokenHolder' = tokenHolder

Spec ==
  Init /\ [][Next]_values /\ WF_vars(Next)

THEOREM Spec => []<>~(tokenHolder = {})
THEOREM Spec => <>(tokenHolder = {1})
```