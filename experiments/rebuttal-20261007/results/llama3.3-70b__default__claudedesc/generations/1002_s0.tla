```
MODULE Barrier
EXTENDS Integers, FiniteSets
CONSTANTS N
VARIABLES pc

Init == (pc = [i \in 1..N |-> "b0"])

b0(self) == pc' = [pc EXCEPT ![self] = "b1"]
b1 == pc' = [i \in 1..N |-> "b0"] /\ pc = [i \in 1..N |-> "b1"]

Next == (\E self \in 1..N : pc[self] = "b0" /\ b0(self)) \/ b1

Spec == Init /\ [][Next]_

TypeOK == pc \in [1..N -> {"b0", "b1"}]
BarrierProperty == []<>(\E i \in 1..N, j \in 1..N : 
                        (pc[i] = "b0" /\ pc[j] = "b1") => pc'[j] = "b1")

THEOREM Spec => []TypeOK
THEOREM Spec => BarrierProperty
```