---------------------------- MODULE Euclid ----------------------------
EXTENDS Naturals

CONSTANT N

VARIABLES pc, u, v, v_ini

vars == <<pc, u, v, v_ini>>

Init ==
    /\ u = 24
    /\ v_ini \in 1..N
    /\ v = v_ini
    /\ pc = "start"

Next ==
    \/ /\ pc = "start"
       /\ u # v
       /\ IF u > v
             THEN /\ u' = u - v
                  /\ v' = v
             ELSE /\ v' = v - u
                  /\ u' = u
       /\ pc' = "start"
       /\ v_ini' = v_ini
    \/ /\ pc = "start"
       /\ u = v
       /\ pc' = "Done"
       /\ UNCHANGED <<u, v, v_ini>>
    \/ /\ pc = "Done"
       /\ FALSE
       /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

TypeOK ==
    /\ u \in Nat
    /\ v \in Nat
    /\ v_ini \in 1..N
    /\ pc \in {"start", "Done"}

GCDProperty ==
    pc = "Done" => u = v

PositiveInvariant ==
    /\ u >= 1
    /\ v >= 1

=======================================================================