```
MODULE Barrier
EXTENDS Integers, FiniteSets

CONSTANTS NumProcs
VARIABLES pc

Init == (pc = [i \in 1..NumProcs |-> "b0"])

Next ==
  /\ pc' = [pc EXCEPT !i = IF pc[i] = "b0" THEN "b1" ELSE "b0"]
  /\ \A i \in 1..NumProcs : pc'[i] = "b0" => \E j \in 1..NumProcs : pc[j] = "b1"

Spec == Init /\ [][Next]_pc

TypeInvariant == pc \in [1..NumProcs -> {"b0", "b1"}]

BarrierProperty == \A i \in 1..NumProcs : <>[]<>(pc[i] = "b1")
                    => [][](pc[i] = "b1" => \A j \in 1..NumProcs : <>[](pc[j] = "b1"))

THEOREM Spec => []TypeInvariant
THEOREM Spec => BarrierProperty
```