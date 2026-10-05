---------------------------- MODULE SubsetRelation ----------------------------
EXTENDS Integers

VARIABLES b

Init == b = TRUE

Next == b' = /\ (SUBSET {} \subseteq SUBSET {})
             /\ (SUBSET {} \subseteq SUBSET {1})
             /\ (SUBSET {} \subseteq SUBSET {1, 2})
             /\ (SUBSET {1} \subseteq SUBSET {1})
             /\ (SUBSET {1} \subseteq SUBSET {1, 2})
             /\ (SUBSET {1, 2} \subseteq SUBSET {1, 2})
             /\ (SUBSET {1} \subseteq SUBSET {1, 2, 3})
             /\ (SUBSET (0..0) \subseteq SUBSET (0..1))
             /\ (SUBSET (1..2) \subseteq SUBSET (1..3))
             /\ (SUBSET (1..3) \subseteq SUBSET (0..5))
             /\ ~(SUBSET {1, 2} \subseteq SUBSET {1})
             /\ ~(SUBSET {1, 2, 3} \subseteq SUBSET {1, 2})
             /\ ~(SUBSET {1} \subseteq SUBSET {2})
             /\ ~(SUBSET {1, 2} \subseteq SUBSET {2, 3})
             /\ ~(SUBSET (0..2) \subseteq SUBSET (1..2))
             /\ ~(SUBSET (1..5) \subseteq SUBSET (2..4))
             /\ (SUBSET {} \subseteq SUBSET Int)
             /\ (SUBSET {} \subseteq SUBSET Nat)
             /\ (SUBSET Nat \subseteq SUBSET Int)
             /\ (SUBSET Nat \subseteq SUBSET Nat)
             /\ (SUBSET Int \subseteq SUBSET Int)
             /\ ~(SUBSET Int \subseteq SUBSET Nat)
             /\ (SUBSET {0, 1, 2} \subseteq SUBSET Nat)
             /\ (SUBSET {-1, 0, 1} \subseteq SUBSET Int)
             /\ ~(SUBSET {-1, 0, 1} \subseteq SUBSET Nat)
             /\ (SUBSET (0..10) \subseteq SUBSET Nat)
             /\ (SUBSET (-5..5) \subseteq SUBSET Int)
             /\ ~(SUBSET (-5..5) \subseteq SUBSET Nat)

Spec == Init /\ [][Next]_b

TypeInvariant == b \in BOOLEAN

Invariant == b = TRUE

===============================================================================