---- MODULE RecursiveSpec ----
EXTENDS Integers

VARIABLES x

\* @type: Int -> Int;
F(n) == IF n = 1 THEN 1 ELSE n + F(n-1)

\* @type: Int -> Bool;
N(i) == x' = x + i

Init == x = 1

Next == (\E i \in {1,2,3} : N(i))
        \/ UNCHANGED x

Spec == Init /\ [][Next]_x

Inv == x < F(5)

====