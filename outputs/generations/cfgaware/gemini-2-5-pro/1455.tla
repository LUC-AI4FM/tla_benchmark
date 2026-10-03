---- MODULE SubsetPowerset ----
EXTENDS Integers

VARIABLES b

Init == b = TRUE

Next ==
    b' = /\ SUBSET {1, 2} \subseteq SUBSET {1, 2, 3}
         /\ ~(SUBSET {1, 2, 3} \subseteq SUBSET {1, 2})
         /\ SUBSET 1..2 \subseteq SUBSET 0..3
         /\ ~(SUBSET 1..3 \subseteq SUBSET 2..4)
         /\ SUBSET Nat \subseteq SUBSET Int
         /\ ~(SUBSET Int \subseteq SUBSET Nat)

Spec == Init /\ [][Next]_b

Invariant == b = TRUE /\ b \in BOOLEAN

=============================================================================