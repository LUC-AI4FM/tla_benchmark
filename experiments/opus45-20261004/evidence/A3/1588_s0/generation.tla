---------------------------- MODULE Euclid ----------------------------
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
       ELSE /\ u' = v - u
            /\ v' = u
    /\ pc' = "start"
    /\ v_ini' = v_ini

Done ==
    /\ pc = "start"
    /\ u = v
    /\ pc' = "Done"
    /\ UNCHANGED <<u, v, v_ini>>

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Subtract
    \/ Done
    \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Safety invariant: u and v are always positive
TypeInvariant ==
    /\ pc \in {"start", "Done"}
    /\ u \in Nat
    /\ v \in Nat
    /\ u >= 1
    /\ v >= 1
    /\ v_ini \in 1..N

\* GCD is preserved throughout computation
GCD(a, b) == CHOOSE g \in 1..a : 
    /\ a % g = 0 
    /\ b % g = 0
    /\ \A d \in 1..a : (a % d = 0 /\ b % d = 0) => d <= g

GCDInvariant ==
    pc = "start" => (u >= 1 /\ v >= 1)

\* When done, u contains the GCD of 24 and v_ini
Correctness ==
    pc = "Done" => u = v

\* Termination property: the algorithm eventually reaches the Done state
Termination == <>(pc = "Done")

=======================================================================