```tla
MODULE BarrierSync

EXTENDS Integers, FiniteSets, TLC

CONSTANTS N
ASSUME N \in Nat /\ N > 0

VARIABLES pc

Init == 
    /\ pc \in [1..N -> {"b0"}]

Next ==
    \/ \/ \E i \in 1..N : /\ pc[i] = "b0"
                             /\ pc' = [pc EXCEPT ![i] = "b1"]
       \/ /\ A i \in 1..N : pc[i] = "b1"
          /\ pc' = [pc EXCEPT ! = "b0"]

TypeOK ==
    pc \in [1..N -> {"b0", "b1"}]

BarrierProperty ==
    \A i \in 1..N, j \in 1..N :
        \/ pc[i] # "b1"
        \/ pc[j] = "b1"

Spec ==
    /\ Init
    /\ [][Next]_<<pc>>
    /\ TypeOK
    /\ BarrierProperty

\* Fairness conditions
WF_spec == WF_next(Init, Next)

SpecWithFairness ==
    Spec /\ WF_spec
```