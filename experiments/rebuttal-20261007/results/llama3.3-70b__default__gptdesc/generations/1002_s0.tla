```
MODULE Barrier
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES pc

Init == (pc = [i \in 1..N |-> "b0"])

Next == \E i \in 1..N :
          /\ pc[i] = "b0"
          /\ pc' = [pc EXCEPT ![i] = "b1"]
        \/ \A i \in 1..N : 
          /\ pc[i] = "b1"
          /\ pc' = [i \in 1..N |-> "b0"]

Spec == Init /\ [][Next]_pc

TypeOK == pc \in [1..N -> {"b0", "b1"}]

BarrierProperty == \A i \in 1..N : 
                   <<pc[i] = "b1">>_{pc} 
                   ~> <>(\A j \in 1..N : pc[j] = "b1")

THEOREM Spec => []TypeOK
THEOREM Spec => BarrierProperty
```