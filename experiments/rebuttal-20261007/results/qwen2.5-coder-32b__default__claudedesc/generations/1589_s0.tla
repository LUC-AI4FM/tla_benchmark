------------------------------- MODULE EuclidGCD -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS MaxNum

VARIABLES pc, u, v, u_ini, v_ini

Init == /\ pc = "a"
        /\ u = u_ini
        /\ v = v_ini
        /\ u_ini \in 1..MaxNum
        /\ v_ini \in 1..MaxNum

GCD(x, y) == CHOOSE d \in {d \in 1..Min(x, y) : x % d = 0 /\ y % d = 0} :
                 \A d' \in {d \in 1..Min(x, y) : x % d = 0 /\ y % d = 0} : d >= d'

Next == \/ /\ pc = "a"
            /\ u # 0
            /\ (/\ u < v
                /\ u' = v
                /\ v' = u
                /\ pc' = "b")
               \/
               (/\ u >= v
                /\ u' = u - v
                /\ v' = v
                /\ pc' = "a")
        \/ /\ pc = "a"
           /\ u = 0
           /\ v = GCD(u_ini, v_ini)
           /\ pc' = "Done"

Spec == Init /\ [][Next]_<<pc, u, v>> /\ WF_next(Next)

Invariant == (pc = "Done" => v = GCD(u_ini, v_ini))

Termination == <>[](pc = "Done")

Finished(s) == s.pc = "Done"
SwapOccurs(t) == t.pc = "a" /\ t.u < t.v

PossibleCounts ==
    /\ TLCGet("States") = 800
    /\ TLCGet("Transitions") = 698

=============================================================================