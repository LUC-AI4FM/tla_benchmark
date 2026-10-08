------------------------------ MODULE SubsetPowerSetTest ------------------------------
CONSTANTS Int, Nat

VARIABLE b

A1  == SUBSET 1..23 \subseteq SUBSET 1..42
A2  == ~ (SUBSET 1..42 \subseteq SUBSET 1..23)
A3  == SUBSET 2..42 \subseteq SUBSET 1..42
A4  == ~ (SUBSET 1..42 \subseteq SUBSET 2..42)
A5  == SUBSET {1,2,3} \subseteq SUBSET {1,2,3,4}
A6  == ~ (SUBSET {1,2,3,4} \subseteq SUBSET {1,2,3})
A7  == SUBSET {} \subseteq SUBSET {}
A8  == SUBSET {} \subseteq SUBSET {1}
A9  == SUBSET {1} \subseteq SUBSET Int
A10 == SUBSET {1} \subseteq SUBSET Nat

Init == b = TRUE

Next == /\ b' = (A1 /\ A2 /\ A3 /\ A4 /\ A5 /\ A6 /\ A7 /\ A8 /\ A9 /\ A10)

Inv  == b /\ (b \in BOOLEAN)

Spec == Init /\ [] [Next]_<<b>>

=============================================================================