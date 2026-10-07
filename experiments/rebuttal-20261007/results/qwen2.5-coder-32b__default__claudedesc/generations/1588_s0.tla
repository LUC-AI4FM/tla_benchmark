------------------------------- MODULE EuclidGCD -------------------------------
EXTENDS Naturals, TLC

CONSTANTS N \* N is a constant bounding the range of v

VARIABLES pc, u, v, v_ini

Init == /\ pc = "lp"
        /\ u = 24
        /\ v \in 1..N
        /\ v_ini = v

Next ==
    \/ /\ pc = "lp"
       /\ (u # 0)
       /\ (/\ u >= v
           /\ pc' = "a"
           /\ u' = u - v
           /\ v' = v
           /\ v_ini' = v_ini)
       \/ (/\ u < v
           /\ pc' = "a"
           /\ u' = v
           /\ v' = u
           /\ v_ini' = v_ini)
    \/ /\ pc = "a"
       /\ pc' = "lp"

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED <<u, v, v_ini>>

Spec ==
    /\ Init
    /\ [][Next]_<<pc, u, v, v_ini>>
    /\ WF_vars(<<pc, u, v, v_ini>>)

GCD(a, b) ==
    LET rec(Gcd, x, y) ==
            IF y = 0 THEN x
            ELSE Gcd(y, x - (x \div y) * y)
    IN rec(GCD, a, b)

Termination == <>(pc = "Done")

=============================================================================