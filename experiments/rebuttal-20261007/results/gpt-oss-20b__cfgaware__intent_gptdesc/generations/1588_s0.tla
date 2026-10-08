------------------------------ MODULE GCD ------------------------------
EXTENDS Naturals

CONSTANTS A, N
ASSUME A > 0 /\ N > 0

VARIABLES x, y, b0

Max(a,b) == IF a >= b THEN a ELSE b

GCD(a,b) ==
    IF b = 0 THEN a
    ELSE GCD(b, a MOD b)

Init ==
    /\ b0 \in 1..N
    /\ x = A
    /\ y = b0

Swap ==
    /\ x < y
    /\ x' = y
    /\ y' = x
    /\ b0' = b0

Subtract ==
    /\ x >= y
    /\ x' = x - y
    /\ y' = y
    /\ b0' = b0

Next == \/ Swap \/ Subtract

Inv ==
    GCD(x,y) = GCD(A,b0)

Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

Termination ==
    <> (x = 0 \/ y = 0)

THEOREM Inv_I == Spec => []Inv
END MODULE