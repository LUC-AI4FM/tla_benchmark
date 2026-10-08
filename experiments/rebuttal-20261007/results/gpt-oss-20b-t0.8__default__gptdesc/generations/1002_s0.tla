MODULE Barrier

EXTENDS Naturals, TLC

CONSTANT N \* number of processes

VARIABLE pc

(* ---------- Definitions ---------- *)

ProcSet == 1 .. N

StateType(pc) ==
    /\ pc \in [ProcSet -> {"b0","b1"}]

Init ==
    StateType(pc)
    /\ pc = [i \in ProcSet |-> "b0"]

IndividualMove(i) ==
    /\ i \in ProcSet
    /\ pc[i] = "b0"
    /\ pc' = [pc EXCEPT ![i] = "b1"]

ResetAll ==
    /\ pc \in [ProcSet -> {"b1"}]
    /\ pc' = [proc \in ProcSet |-> "b0"]

Next ==
    (\E i \in ProcSet : IndividualMove(i))
    \/ ResetAll

TypeInvariant == StateType(pc)

NoPartialReset ==
    (* No process may leave the barrier individually while some other
       process has not yet entered it. *)
    \A i \in ProcSet :
        /\ pc[i] = "b1"
        /\ (\E j \in ProcSet : pc[j] = "b0")
        => NOT (pc' = [pc EXCEPT ![i] = "b0"])

Spec == Init
       /\ []Next
       /\ []TypeInvariant
       /\ []NoPartialReset

===============================================================================