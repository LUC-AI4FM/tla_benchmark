---------------------------- MODULE Barrier --------------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLE pc

TypeOK == pc \in [1..N -> {"b0", "b1"}]

b0(self) == pc' = [pc EXCEPT ![self] = "b1"]

b1 == (pc = [i \in 1..N |-> "b1"]) /\ pc' = [i \in 1..N |-> "b0"]

Next == \E self \in 1..N : b0(self) \/ b1

Spec == Init /\ [][Next]_pc

Init == pc = [i \in 1..N |-> "b0"]

BarrierProperty == \A self \in 1..N, other \in 1..N :
                    (self # other) => 
                    [](pc[self] = "b0" /\ pc[other] = "b1" => pc'[other] = "b1")

THEOREM Spec => []TypeOK
THEOREM Spec => BarrierProperty

=============================================================================