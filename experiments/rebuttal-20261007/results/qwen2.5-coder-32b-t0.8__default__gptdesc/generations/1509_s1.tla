---- MODULE SmallSystem ----

EXTENDS Naturals

CONSTANTS 
    F

VARIABLES x

Init == x \in {1, 2, 3, 4, 5}

F[1] == 2
F[n] == IF n = 5 THEN 1 ELSE n + 1

N[1] == x' \in {x, F[x]}
N[2] == x' \in {x, F[F[x]]}
N[3] == x' \in {x, F[F[F[x]]]}

Next == \/ /\ EXISTS i \in {1, 2, 3} : N[i]
          \/ x' = x

Inv == x \in {1, 2, 3, 4, 5}

Spec == Init /\ [][Next]_x /\ <>[][Inv]_<<x>>

====