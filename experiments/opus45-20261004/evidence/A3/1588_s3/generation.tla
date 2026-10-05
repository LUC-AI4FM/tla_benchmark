---------------------------- MODULE euclid ----------------------------
EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat /\ N >= 1

VARIABLES pc, u, v, v_ini

vars == <<pc, u, v, v_ini>>

Init ==
    /\ pc = "start"
    /\ u = 24
    /\ v_ini \in 1..N
    /\ v = v_ini

Subtract ==
    /\ pc = "start"
    /\ u /= v
    /\ IF u > v
       THEN /\ u' = u - v
            /\ v' = v
       ELSE /\ v' = v - u
            /\ u' = u
    /\ pc' = "start"
    /\ v_ini' = v_ini

Terminate ==
    /\ pc = "start"
    /\ u = v
    /\ pc' = "Done"
    /\ UNCHANGED <<u, v, v_ini>>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Subtract
    \/ Terminate
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

TypeOK ==
    /\ pc \in {"start", "Done"}
    /\ u \in Nat
    /\ v \in Nat
    /\ v_ini \in 1..N

GCDProperty ==
    pc = "Done" => u = v

PositiveInvariant ==
    /\ u >= 1
    /\ v >= 1

=======================================================================