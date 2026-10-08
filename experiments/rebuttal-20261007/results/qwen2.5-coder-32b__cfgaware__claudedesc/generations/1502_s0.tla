------------------------------- MODULE TestModule -------------------------------

CONSTANTS Id, Forty2, Op

VARIABLES x

Init == x = 0

Next == /\ \/ \E y \in SUBSET {1,2,3} : x' = y
         /\ UNCHANGED << >>

Id(n) == SUBSET {1,2,3}

Forty2(n) == Id(n)

Op(x) == Forty2(x)

===============================================================================