------------------------------ MODULE Barrier ------------------------------
EXTENDS Naturals

CONSTANT N

VARIABLE state

(* Process identifiers *)
ProcSet == 1..N

(* State values *)
Ready   == 0
Arrived == 1

Init == state = [p \in ProcSet |-> Ready]

(* Individual arrival action for a process p *)
Arrive(p) ==
    /\ p \in ProcSet
    /\ state[p] = Ready
    /\ state' = [state EXCEPT ![p] = Arrived]

(* Collective release action: all processes move from Arrived to Ready atomically *)
Release ==
    /\ \A p \in ProcSet : state[p] = Arrived
    /\ state' = [state EXCEPT ![i] = Ready |-> TRUE]

(* Stuttering step *)
Stutter == state' = state

Next == Release \/ Stutter \/ \E p \in ProcSet : Arrive(p)

Spec == Init /\ [][Next]_state

TypeOK == state \in [ProcSet -> {Ready, Arrived}]

BarrierProperty ==
    [] ((\E p \in ProcSet : state[p] = Arrived /\ state'[p] = Ready)
        => (\A q \in ProcSet : state[q] = Arrived))

THEOREM Spec_implies_TypeOK == Spec => [] TypeOK

END MODULE