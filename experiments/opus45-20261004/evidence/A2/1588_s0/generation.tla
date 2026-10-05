---------------------------- MODULE EuclidGCD ----------------------------
EXTENDS Integers, Naturals, TLC

CONSTANT N

VARIABLES pc, u, v, v_ini

vars == <<pc, u, v, v_ini>>

-----------------------------------------------------------------------------
(* Reference GCD operator *)
GCD(a, b) == CHOOSE g \in 1..a : 
               /\ a % g = 0 
               /\ b % g = 0
               /\ \A d \in 1..a : (a % d = 0 /\ b % d = 0) => d <= g

-----------------------------------------------------------------------------
(* Initial state *)
Init == 
    /\ pc = "lp"
    /\ u = 24
    /\ v \in 1..N
    /\ v_ini = v

-----------------------------------------------------------------------------
(* Actions *)

(* At label lp: check if u /= 0, swap if needed, go to a; else print and go to Done *)
Lp == 
    /\ pc = "lp"
    /\ IF u /= 0
       THEN /\ IF u < v
               THEN /\ u' = v
                    /\ v' = u
               ELSE /\ u' = u
                    /\ v' = v
            /\ pc' = "a"
            /\ v_ini' = v_ini
       ELSE /\ PrintT(<<"GCD of 24 and", v_ini, "is", v>>)
            /\ pc' = "Done"
            /\ u' = u
            /\ v' = v
            /\ v_ini' = v_ini

(* At label a: subtract v from u, return to lp *)
A == 
    /\ pc = "a"
    /\ u' = u - v
    /\ v' = v
    /\ v_ini' = v_ini
    /\ pc' = "lp"

(* Terminating action: stutter when Done *)
Terminating == 
    /\ pc = "Done"
    /\ UNCHANGED vars

-----------------------------------------------------------------------------
(* Next-state relation *)
Next == Lp \/ A \/ Terminating

-----------------------------------------------------------------------------
(* Specification with weak fairness *)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Liveness property: Termination *)
Termination == <>(pc = "Done")

=============================================================================