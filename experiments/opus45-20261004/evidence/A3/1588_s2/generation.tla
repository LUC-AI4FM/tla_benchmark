---------------------------- MODULE euclid ----------------------------
EXTENDS Naturals, TLC

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
       /\ UNCHANGED v_ini
    \/ /\ pc = "start"
       /\ u = v
       /\ pc' = "Done"
       /\ UNCHANGED <<u, v, v_ini>>
    \/ /\ pc = "Done"
       /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

TypeInvariant ==
    /\ u \in Nat
    /\ v \in Nat
    /\ v_ini \in 1..N
    /\ pc \in {"start", "Done"}

GCDCorrectness ==
    pc = "Done" => u = v

PositiveInvariant ==
    /\ u >= 1
    /\ v >= 1

=======================================================================