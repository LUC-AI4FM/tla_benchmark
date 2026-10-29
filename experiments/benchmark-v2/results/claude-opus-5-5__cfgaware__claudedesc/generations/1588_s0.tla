---------------------------- MODULE Euclid ----------------------------
EXTENDS Naturals, TLC

CONSTANT N

Divides(p, n) == \E q \in 0..n : n = q * p
DivisorsOf(n) == {p \in 1..n : Divides(p, n)}
SetMax(S) == CHOOSE x \in S : \A y \in S : x >= y
GCD(m, n) == SetMax(DivisorsOf(m) \cap DivisorsOf(n))

VARIABLES pc, u, v, v_ini

vars == << pc, u, v, v_ini >>

Init == /\ u = 24
        /\ v \in 1..N
        /\ v_ini = v
        /\ pc = "lp"

lp == /\ pc = "lp"
      /\ IF u # 0
            THEN /\ IF u < v
                       THEN /\ u' = v
                            /\ v' = u
                       ELSE /\ UNCHANGED << u, v >>
                 /\ pc' = "a"
            ELSE /\ PrintT(<<24, v_ini, "have gcd", v>>)
                 /\ pc' = "Done"
                 /\ UNCHANGED << u, v >>
      /\ UNCHANGED v_ini

a == /\ pc = "a"
     /\ u' = u - v
     /\ pc' = "lp"
     /\ UNCHANGED << v, v_ini >>

Terminating == /\ pc = "Done"
               /\ UNCHANGED vars

Next == lp \/ a \/ Terminating

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

=============================================================================