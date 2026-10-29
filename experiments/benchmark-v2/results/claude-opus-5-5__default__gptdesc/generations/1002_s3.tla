------------------------------ MODULE Barrier ------------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssump == N \in Nat \ {0}

VARIABLE pc

vars == << pc >>

ProcSet == 1..N

-----------------------------------------------------------------------------

Init == pc = [p \in ProcSet |-> "b0"]

(* A single process enters the barrier. *)
Enter(p) == /\ pc[p] = "b0"
            /\ pc' = [pc EXCEPT ![p] = "b1"]

(* Once every process is in the barrier, all are released together. *)
Release == /\ \A p \in ProcSet : pc[p] = "b1"
           /\ pc' = [p \in ProcSet |-> "b0"]

Next == \/ \E p \in ProcSet : Enter(p)
        \/ Release

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

TypeOK == pc \in [ProcSet -> {"b0", "b1"}]

(* A process may leave the barrier (go from "b1" back to "b0") only if   *)
(* every process has already entered the barrier.                       *)
BarrierProperty ==
    \A p \in ProcSet :
        [][ (pc[p] = "b1" /\ pc'[p] = "b0")
              => (\A q \in ProcSet : pc[q] = "b1") ]_pc

THEOREM Spec => []TypeOK
THEOREM Spec => BarrierProperty
=============================================================================