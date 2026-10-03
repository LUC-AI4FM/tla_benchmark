---------------------------- MODULE Barrier ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N > 0

VARIABLE pc

Procs == 1..N

TypeOK == pc \in [Procs -> {"b0", "b1"}]

Init == pc = [i \in Procs |-> "b0"]

Enter(i) == /\ pc[i] = "b0"
            /\ pc' = [pc EXCEPT ![i] = "b1"]

Reset == /\ \A i \in Procs : pc[i] = "b1"
         /\ pc' = [i \in Procs |-> "b0"]

Next == \/ \E i \in Procs : Enter(i)
        \/ Reset

Spec == Init /\ [][Next]_pc

BarrierProperty == \A i \in Procs : \A j \in Procs :
                     (pc[j] = "b0" /\ i # j) => pc[i] # "b0"

==========================================================================