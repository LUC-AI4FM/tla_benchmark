---------------------------- MODULE CyclicBarrier ----------------------------

EXTENDS Integers

CONSTANT N

VARIABLE pc

Procs == 1..N

Locations == {"b0", "b1"}

TypeOK == pc \in [Procs -> Locations]

Init == pc = [p \in Procs |-> "b0"]

b0(self) == /\ pc[self] = "b0"
            /\ pc' = [pc EXCEPT ![self] = "b1"]

b1 == /\ \A p \in Procs : pc[p] = "b1"
      /\ pc' = [p \in Procs |-> "b0"]

Next == \/ \E self \in Procs : b0(self)
        \/ b1

Spec == Init /\ [][Next]_pc

BarrierProperty == \A p, q \in Procs :
                     (pc[p] = "b0" /\ pc[q] = "b1") => pc'[q] = "b1"

=============================================================================