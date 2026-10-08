------------------------------ MODULE SmallSpec ------------------------------
EXTENDS TLC

VARIABLE x

\* Recursive function-like operator F over the set {1,2,3,4,5}
F(x) == IF x = 1 THEN 2
          ELSE IF x \in {2,3,4,5} THEN F(x-1) + 1
          ELSE 0   \* value for out‑of‑domain arguments (not used)

\* Indexed action N over the set {1,2,3}
N(i) == /\ i \in 1..3
        /\ x' = x + i

Init == /\ x \in 1..5
       /\ x = 1

Next == EXISTS i \in 1..3 : N(i)

Inv == x \in 1..5

Spec == Init /\ [] [Next]_x /\ [] Inv

=============================================================================