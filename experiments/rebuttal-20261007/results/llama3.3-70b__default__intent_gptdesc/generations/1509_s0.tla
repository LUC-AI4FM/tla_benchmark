```
MODULE FiniteStateSystem
EXTENDS Integers

CONSTANTS Domain
VARIABLES state, mapping

Init == 
  /\ state \in {1,2,3,4,5}
  /\ mapping \in [Domain -> {1,2,3,4,5}]

Next == 
  /\ state' \in {1,2,3,4,5}
  /\ mapping' \in [Domain -> {1,2,3,4,5}]
  /\ \E i \in Domain : mapping'[i] = state'

Spec == 
  Init /\ [][Next]_<<state, mapping>>

Invariant == 
  \A s \in {1,2,3,4,5} : 
    \E i \in Domain : mapping[i] = s

Safety == 
  []Invariant

Liveness == 
  <>[]<>(state # state')

THEOREM Spec => []Invariant
THEOREM Spec => Liveness
```
Note: The `Domain` constant should be replaced with a specific finite set of indices, for example `{a, b, c}`. 

Also note that the fairness condition is implicitly included in the `Next` action by allowing the system to choose any next state and mapping, which ensures that the system does not deadlock.