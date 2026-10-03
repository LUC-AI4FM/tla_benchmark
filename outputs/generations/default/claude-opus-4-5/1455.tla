---------------------------- MODULE SubsetRelation ----------------------------
EXTENDS Integers, FiniteSets

VARIABLES b

Init == b = TRUE

Next == b' = (
    \* Positive cases - should be TRUE
    /\ (SUBSET {} \subseteq SUBSET {})
    /\ (SUBSET {} \subseteq SUBSET {1})
    /\ (SUBSET {} \subseteq SUBSET {1, 2})
    /\ (SUBSET {1} \subseteq SUBSET {1, 2})
    /\ (SUBSET {1} \subseteq SUBSET {1, 2, 3})
    /\ (SUBSET {1, 2} \subseteq SUBSET {1, 2, 3})
    /\ (SUBSET {1, 2} \subseteq SUBSET {1, 2})
    /\ (SUBSET (1..2) \subseteq SUBSET (1..3))
    /\ (SUBSET (1..1) \subseteq SUBSET (1..2))
    /\ (SUBSET (0..0) \subseteq SUBSET (0..1))
    /\ (SUBSET {"a"} \subseteq SUBSET {"a", "b"})
    /\ (SUBSET {"a", "b"} \subseteq SUBSET {"a", "b", "c"})
    /\ (SUBSET Nat \subseteq SUBSET Int)
    /\ (SUBSET Nat \subseteq SUBSET Nat)
    /\ (SUBSET Int \subseteq SUBSET Int)
    \* Negated cases - should be TRUE (the negation of false statements)
    /\ ~(SUBSET {1, 2} \subseteq SUBSET {1})
    /\ ~(SUBSET {1, 2, 3} \subseteq SUBSET {1, 2})
    /\ ~(SUBSET {1} \subseteq SUBSET {})
    /\ ~(SUBSET (1..3) \subseteq SUBSET (1..2))
    /\ ~(SUBSET (1..2) \subseteq SUBSET (1..1))
    /\ ~(SUBSET {"a", "b"} \subseteq SUBSET {"a"})
    /\ ~(SUBSET {"a", "b", "c"} \subseteq SUBSET {"a", "b"})
    /\ ~(SUBSET Int \subseteq SUBSET Nat)
    /\ ~(SUBSET {1, 2} \subseteq SUBSET {3, 4})
    /\ ~(SUBSET {1} \subseteq SUBSET {2})
)

Spec == Init /\ [][Next]_b

TypeInvariant == b \in BOOLEAN

SafetyInvariant == b = TRUE

Invariant == SafetyInvariant /\ TypeInvariant

===============================================================================