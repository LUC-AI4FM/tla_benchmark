------------------------------- MODULE CyclicBarrier -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N
ASSUME N \in Nat /\ N > 0

VARIABLES pc

Init == /\ pc \in [1..N -> {"b0"}]

b0(self) == 
    /\ self \in 1..N
    /\ pc[self] = "b0"
    /\ pc' = [pc EXCEPT ![self] = "b1"]

b1 ==
    /\ (\A p \in 1..N : pc[p] = "b1")
    /\ pc' = [p \in 1..N -> "b0"]

Next == 
    \/ \E self \in 1..N : b0(self)
    \/ b1

Spec == Init /\ [][Next]_<<pc>>

TypeOK == \A p \in 1..N : pc[p] \in {"b0", "b1"}

BarrierProperty ==
    ~(\E p1, p2 \in 1..N : pc[p1] = "b0" /\ pc[p2] = "b1") \/ 
    (\A p \in 1..N : pc'[p] # "b0")

=============================================================================