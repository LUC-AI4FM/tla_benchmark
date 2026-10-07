MODULE EuclidSubtraction

EXTENDS Integers

CONSTANT N

VARIABLES pc, u, v, v_ini

vars == <<pc,u,v,v_ini>>

Init ==
    /\ pc = "lp"
    /\ u = 24
    /\ v \in 1..N
    /\ v_ini = v

LpNonZeroSwap ==
    /\ pc = "lp"
    /\ u /= 0
    /\ u < v
    /\ u' = v
    /\ v' = u
    /\ pc' = "a"

LpNonZeroNoSwap ==
    /\ pc = "lp"
    /\ u /= 0
    /\ u >= v
    /\ UNCHANGED <<u,v>>
    /\ pc' = "a"

LpZero ==
    /\ pc = "lp"
    /\ u = 0
    /\ pc' = "Done"
    /\ UNCHANGED <<u,v>>

AAction ==
    /\ pc = "a"
    /\ u' = u - v
    /\ v' = v
    /\ pc' = "lp"

Terminate ==
    /\ pc = "Done"
    /\ UNCHANGED <<pc,u,v,v_ini>>

Next == LpNonZeroSwap \/ LpNonZeroNoSwap \/ LpZero \/ AAction \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <> (pc = "Done")

GCD(a,b) ==
    IF b = 0 THEN a ELSE GCD(b, a % b)

END MODULE