---------------------------- MODULE euclid ----------------------------
EXTENDS Integers, Naturals, TLC

CONSTANT N

VARIABLES pc, u, v, v_ini

vars == <<pc, u, v, v_ini>>

GCD(a, b) == 
    LET RECURSIVE GCDHelper(_, _)
        GCDHelper(x, y) == IF y = 0 THEN x ELSE GCDHelper(y, x % y)
    IN GCDHelper(a, b)

Init ==
    /\ pc = "lp"
    /\ u = 24
    /\ v \in 1..N
    /\ v_ini = v

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

A ==
    /\ pc = "a"
    /\ u' = u - v
    /\ v' = v
    /\ v_ini' = v_ini
    /\ pc' = "lp"

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Lp
    \/ A
    \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

=======================================================================