---- MODULE Barrier ----
EXTENDS Integers, TLC

CONSTANT N
ASSUME N \in Nat \ {0}

Procs == 1..N
States == {"b0", "b1"}

VARIABLE pc

vars == <<pc>>

TypeOK == pc \in [Procs -> States]

Init == pc = [p \in Procs |-> "b0"]

Enter(p) == /\ pc[p] = "b0"
            /\ pc' = [pc EXCEPT ![p] = "b1"]

Reset == /\ \A p \in Procs : pc[p] = "b1"
         /\ pc' = [p \in Procs |-> "b0"]

Next == \/ (\E p \in Procs : Enter(p))
        \/ Reset

Spec == Init /\ [][Next]_vars

BarrierProperty ==
    [](\A p \in Procs :
        (pc[p] = "b1" /\ pc'[p] = "b0") => (\A q \in Procs : pc[q] = "b1"))

=============================================================================