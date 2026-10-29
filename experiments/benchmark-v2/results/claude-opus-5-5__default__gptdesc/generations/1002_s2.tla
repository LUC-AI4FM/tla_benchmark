---------------------------- MODULE Barrier ----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

ProcSet == 1..N

VARIABLE pc

vars == << pc >>

-----------------------------------------------------------------------------
TypeOK == pc \in [ProcSet -> {"b0", "b1"}]

Init == pc = [p \in ProcSet |-> "b0"]

(* A single process enters the barrier. *)
Enter(p) ==
    /\ pc[p] = "b0"
    /\ pc' = [pc EXCEPT ![p] = "b1"]

(* Once all processes are in the barrier, they are all released together. *)
Release ==
    /\ \A q \in ProcSet : pc[q] = "b1"
    /\ pc' = [q \in ProcSet |-> "b0"]

Next == (\E p \in ProcSet : Enter(p)) \/ Release

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* A process may leave the barrier (go from b1 to b0) only if every       *)
(* process has already entered the barrier.                               *)
BarrierProperty ==
    [][\A p \in ProcSet :
          (pc[p] = "b1" /\ pc'[p] = "b0") => (\A q \in ProcSet : pc[q] = "b1")
      ]_vars

THEOREM Spec => []TypeOK
THEOREM Spec => BarrierProperty
=============================================================================