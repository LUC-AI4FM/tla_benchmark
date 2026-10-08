```
MODULE TerminationDetection
EXTENDS Integers, Sequences

CONSTANTS Node

VARIABLES state, detected

Init ==
  /\ state \in [Node -> {<<"active">>, <<"inactive">>}]
  /\ detected = FALSE

Next ==
  \/ \E n \in Node : 
    /\ state[n] = <<"active">>
    /\ state' = [state EXCEPT ![n] = <<"inactive">>]
    /\ detected' = detected
  \/ \E n \in Node :
    /\ state[n] = <<"active">>
    /\ \E m \in Node : 
      /\ m /= n
      /\ state[m] = <<"inactive">>
      /\ state' = [state EXCEPT ![m] = <<"active">>]
      /\ detected' = detected
  \/ /\ detected' = TRUE
     /\ \A n \in Node : state[n] = <<"inactive">>
     /\ state' = state

Spec == Init /\ [][Next]_<<state, detected>>
WeakFairness == <>[]<detected'_> 

THEOREM Spec => []<>(detected')
```