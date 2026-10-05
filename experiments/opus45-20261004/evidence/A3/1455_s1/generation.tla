---------------------------- MODULE SubsetRelation ----------------------------
EXTENDS Integers

VARIABLES b

Init == b = TRUE

Next == b' = /\ (SUBSET {} \subseteq SUBSET {})
             /\ (SUBSET {1} \subseteq SUBSET {1, 2})
             /\ (SUBSET {1, 2} \subseteq SUBSET {1, 2, 3})
             /\ (SUBSET {} \subseteq SUBSET {1})
             /\ (SUBSET {1} \subseteq SUBSET {1})
             /\ (SUBSET (1..2) \subseteq SUBSET (1..3))
             /\ (SUBSET (1..1) \subseteq SUBSET (1..2))
             /\ (SUBSET {} \subseteq SUBSET (1..5))
             /\ (SUBSET {"a"} \subseteq SUBSET {"a", "b"})
             /\ (SUBSET {"a", "b"} \subseteq SUBSET {"a", "b", "c"})
             /\ ~(SUBSET {1, 2} \subseteq SUBSET {1})
             /\ ~(SUBSET {1, 2, 3} \subseteq SUBSET {1, 2})
             /\ ~(SUBSET (1..3) \subseteq SUBSET (1..2))
             /\ ~(SUBSET {"a", "b"} \subseteq SUBSET {"a"})
             /\ ~(SUBSET {1} \subseteq SUBSET {})
             /\ (SUBSET Nat \subseteq SUBSET Int)
             /\ ~(SUBSET Int \subseteq SUBSET Nat)
             /\ (SUBSET {} \subseteq SUBSET Nat)
             /\ (SUBSET {} \subseteq SUBSET Int)
             /\ (SUBSET {0, 1, 2} \subseteq SUBSET Nat)
             /\ (SUBSET {-1, 0, 1} \subseteq SUBSET Int)
             /\ ~(SUBSET {-1} \subseteq SUBSET Nat)

Spec == Init /\ [][Next]_b

TypeInvariant == b \in BOOLEAN

SafetyInvariant == b = TRUE

Invariant == TypeInvariant /\ SafetyInvariant

=============================================================================