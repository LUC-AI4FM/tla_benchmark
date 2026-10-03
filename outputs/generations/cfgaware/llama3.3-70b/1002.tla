---------------------------- MODULE Barrier --------------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLE pc

TypeOK == pc \in [1..N -> {"b0", "b1"}]

Spec == /\ pc = [i \in 1..N |-> "b0"]
       /\ [][
           /\ \A i \in 1..N : 
               pc[i] = "b0" \/ (pc[i] = "b1" /\ pc' = [pc EXCEPT ![i] = "b0"])
           /\ (\A i \in 1..N : pc[i] = "b1") => pc' = [i \in 1..N |-> "b0"]
           /\ TypeOK'
         ]

BarrierProperty == \A i \in 1..N : 
                   []<>(pc[i] = "b1") => <>[](~(\E j \in 1..N : pc[j] = "b0"))

=============================================================================