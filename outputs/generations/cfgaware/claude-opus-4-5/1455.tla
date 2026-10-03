---------------------------- MODULE spec ----------------------------

EXTENDS Integers, FiniteSets

VARIABLE b

Init == b = TRUE

Next == b' = /\ (SUBSET {} \subseteq SUBSET {})
             /\ (SUBSET {1} \subseteq SUBSET {1, 2})
             /\ (SUBSET {1, 2} \subseteq SUBSET {1, 2, 3})
             /\ (SUBSET {} \subseteq SUBSET {1})
             /\ (SUBSET {1} \subseteq SUBSET {1})
             /\ ~(SUBSET {1, 2} \subseteq SUBSET {1})
             /\ ~(SUBSET {1, 2, 3} \subseteq SUBSET {1, 2})
             /\ (SUBSET (1..1) \subseteq SUBSET (1..2))
             /\ (SUBSET (1..2) \subseteq SUBSET (1..3))
             /\ ~(SUBSET (1..3) \subseteq SUBSET (1..2))
             /\ (SUBSET {} \subseteq SUBSET (0..5))
             /\ (SUBSET {0, 1} \subseteq SUBSET (0..10))
             /\ ~(SUBSET (1..5) \subseteq SUBSET {1, 2, 3})
             /\ (SUBSET Nat \subseteq SUBSET Int)
             /\ ~(SUBSET Int \subseteq SUBSET Nat)

Spec == Init /\ [][Next]_b

Inv == b = TRUE /\ b \in BOOLEAN

==========================================================================