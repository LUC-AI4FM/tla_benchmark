```
MODULE DijkstraTokenRing
EXTENDS Integers

CONSTANTS N, K
VARIABLES values, tokenHolder

Init == (values = [i \in 0..N-1 |-> 0] /\ tokenHolder = {})

Next == 
  \/ (\E i \in 0..N-1 : 
        IF i = 0 
        THEN values' = [values EXCEPT ![0] = (values[0] + 1) % K]
        ELSE values' = [values EXCEPT ![i] = values[(i-1) % N]]
      )
  \/ (\E i \in 0..N-1 : 
        tokenHolder' = IF i = 0 /\ values[i] = values[(N-1) % N] 
                       THEN {i} 
                       ELSE {}
      )

Spec == Init /\ [][Next]_values /\ WF_vars(Next)

THEOREM Spec => []<>(\E i \in 0..N-1 : tokenHolder = {i})
THEOREM Spec => <>(\E i \in 0..N-1 : tokenHolder = {i} /\ \A j \in 0..N-1 : j /= i => values[j] /= values[i])
```