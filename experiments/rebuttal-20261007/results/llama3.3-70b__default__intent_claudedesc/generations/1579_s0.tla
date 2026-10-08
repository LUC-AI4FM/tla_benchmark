```
MODULE TokenRing
EXTENDS Integers

CONSTANTS N, K
VARIABLES values, tokenHolders

Init ==
  /\ values = [i \in 0..N-1 |-> 0]
  /\ tokenHolders = {}

Next ==
  \/ \E i \in 0..N-1 :
    /\ (i = 0) => (values[0] = values[(N-1)]) 
    /\ (i # 0) => (values[i] # values[(i-1)%N])
    /\ values' = [values EXCEPT ![i] = IF i = 0 THEN (values[i] + 1) % K ELSE values[(i-1)%N]]
    /\ tokenHolders' = {}
  \/ tokenHolders' = {}
  /\ values' = values

Spec ==
  Init /\ [][Next]_values

SafetyInv ==
  \E i \in 0..N-1 : 
    (i = 0) => (values[0] = values[(N-1)]) 
    \/ (i # 0) => (values[i] # values[(i-1)%N])

LivenessProp ==
  <>(\E i \in 0..N-1 : 
      /\ ((i = 0) => (values[0] = values[(N-1)]))
      /\ (\A j \in 0..N-1 : j # i => 
          ((j = 0) => (values[j] # values[(N-1)]) 
           \/ (j # 0) => (values[j] = values[(j-1)%N])))
      /\ []((i = 0) => (values[0] = values[(N-1)]))
      )

THEOREM Spec => []SafetyInv
THEOREM Spec => LivenessProp

Fairness ==
  WF_vars(Next, values)
```
Note: The `WF_vars` operator is used to specify weak fairness for the `Next` action with respect to the `values` variable. This ensures that if a process is continuously enabled to act, it will eventually be scheduled.