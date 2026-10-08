```
MODULE Barrier
EXTENDS Integers
CONSTANTS N
VARIABLES pc

Init == (* Initialize each process to state "b0" *)
        pc = [i \in 1..N |-> "b0"]

Next == (* Define the next-state relation for a single step of any process i *)
        \E i \in 1..N :
          (pc[i] = "b0" /\ pc' = [pc EXCEPT ![i] = "b1"]) \/
          (pc[i] = "b1" /\ \A j \in 1..N : pc[j] = "b1" /\ pc' = [i \in 1..N |-> "b0"])

Spec == Init /\ [][Next]_pc

TypeCorrectness == 
        pc \in [1..N -> {"b0", "b1"}]

BarrierProperty == 
        \A i \in 1..N : <<pc[i] = "b1">>_{pc} >> (pc[i] = "b1")_{pc}

THEOREM Spec => []TypeCorrectness
THEOREM Spec => BarrierProperty
```