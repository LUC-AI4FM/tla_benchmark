MODULE RecFuncSpec
EXTENDS Naturals

VARIABLES x

F == [i \in 1..5 |-> IF i = 1 THEN 1 ELSE (F)[i - 1] + 1]

N(i) == /\ i \in 1..3
          /\ x' = (F)[i]

Init == /\ x \in 1..5
        /\ x = (F)[1]

Next == \E i \in 1..3 : N(i)

Inv == /\ x \in DOMAIN F
        /\ x = (F)[x]

Spec == Init /\ [][ Next ]_x

===============================================================================