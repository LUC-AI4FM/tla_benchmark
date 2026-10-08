```
MODULE Barrier
EXTENDS Integers

CONSTANTS N
VARIABLES pc

Init == (* Initial state: all processes in "b0" *)
        pc = [i \in 1..N |-> "b0"]

Next == (* Next-state relation *)
        /\ pc' = [pc EXCEPT ![i] = IF pc[i] = "b0" THEN "b1" ELSE "b0"]
        /\ \A i \in 1..N : pc[i] = "b1" => pc'[i] = "b0"

Spec == Init /\ [][Next]_pc

TypeCorrectness == (* Type correctness condition *)
                   pc \in [1..N -> {"b0", "b1"}]

BarrierProperty == (* Temporal barrier property *)
                   \A i \in 1..N : pc[i] = "b1" => <>\<<pc[j] = "b1">>_{j \in 1..N}

THEOREM Spec => []TypeCorrectness
THEOREM Spec => BarrierProperty
```