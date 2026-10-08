```
MODULE Barrier
EXTENDS Integers, TLC
CONSTANTS N
VARIABLES pc

Init == (* Initialize all processes to "b0" *)
        pc = [i \in 1..N |-> "b0"]

Next == (* Each process can move from "b0" to "b1" or stay in "b1" if not all have reached "b1", 
           otherwise reset all to "b0" *)
        /\ pc' = [i \in 1..N |-> IF pc[i] = "b0" THEN "b1" ELSE IF \A j \in 1..N : pc[j] = "b1" THEN "b0" ELSE pc[i]]

Spec == Init /\ [][Next]_pc

TypeInvariant == pc \in [1..N -> {"b0", "b1"}]

TemporalBarrierProperty == []<>(\E i \in 1..N : pc[i] = "b1") => <>[\A i \in 1..N : pc[i] = "b1"]

THEOREM Spec => []TypeInvariant
THEOREM Spec => TemporalBarrierProperty
```