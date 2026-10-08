```
MODULE DijkstraTokenRing
EXTENDS Integers, FiniteSets

CONSTANTS N, K
ASSUME N > 0 & K > N

VARIABLES values, tokenHolders

Init == 
  /\ values = [i \in 0..N-1 |-> 0]
  /\ tokenHolders = {}

Next == 
  \/ /\ ~tokenHolders = {}
     /\ values[0] = values[N-1]
     /\ values' = [values EXCEPT ![0] = (values[0] + 1) % K]
     /\ tokenHolders' = {0}
  \/ /\ tokenHolders /= {}
     /\ \E i \in 0..N-2 :
        /\ values[i+1] /= values[i]
        /\ values' = [values EXCEPT ![i+1] = values[i]]
        /\ tokenHolders' = IF values'[i+1] = values'[i-1] THEN {i+1} ELSE {}
  \/ /\ ~tokenHolders = {}
     /\ \E i \in 0..N-2 :
        /\ values[i+1] /= values[i]
        /\ values' = [values EXCEPT ![i+1] = values[i]]
        /\ tokenHolders' = {}

Spec == Init /\ [][Next]_<<values, tokenHolders>>
           /\ WF_vars(<<values, tokenHolders>>)

THEOREM Spec => []<>~(tokenHolders = {})
THEOREM Spec => <>(tokenHolders = {some i \in 0..N-1 : TRUE})
```