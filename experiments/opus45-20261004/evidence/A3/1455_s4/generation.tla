---------------------------- MODULE SubsetRelation ----------------------------

EXTENDS Integers

VARIABLES b

Init == b = TRUE

Next == b' = (
    \* Positive cases - these should all be TRUE
    
    \* Empty set is subset of any powerset
    /\ (SUBSET {} \subseteq SUBSET {})
    /\ (SUBSET {} \subseteq SUBSET {1, 2, 3})
    
    \* SUBSET of smaller set is subset of SUBSET of larger set
    /\ (SUBSET {1} \subseteq SUBSET {1, 2})
    /\ (SUBSET {1, 2} \subseteq SUBSET {1, 2, 3})
    /\ (SUBSET {1} \subseteq SUBSET {1, 2, 3})
    
    \* SUBSET of a set is subset of SUBSET of itself
    /\ (SUBSET {1, 2, 3} \subseteq SUBSET {1, 2, 3})
    /\ (SUBSET {} \subseteq SUBSET {})
    
    \* Integer ranges
    /\ (SUBSET (0..1) \subseteq SUBSET (0..2))
    /\ (SUBSET (1..2) \subseteq SUBSET (0..3))
    /\ (SUBSET (0..0) \subseteq SUBSET (0..1))
    
    \* Finite enumerated sets with various elements
    /\ (SUBSET {0} \subseteq SUBSET {0, 1})
    /\ (SUBSET {1, 2} \subseteq SUBSET {1, 2, 3, 4})
    
    \* Negated cases - these negations should all be TRUE
    \* (meaning the original subset relation is FALSE)
    
    \* SUBSET of larger set is NOT subset of SUBSET of smaller set
    /\ ~(SUBSET {1, 2} \subseteq SUBSET {1})
    /\ ~(SUBSET {1, 2, 3} \subseteq SUBSET {1, 2})
    /\ ~(SUBSET {1, 2, 3} \subseteq SUBSET {1})
    
    \* Disjoint sets
    /\ ~(SUBSET {1} \subseteq SUBSET {2})
    /\ ~(SUBSET {1, 2} \subseteq SUBSET {3, 4})
    
    \* Partially overlapping sets where first is not subset of second
    /\ ~(SUBSET {1, 2, 3} \subseteq SUBSET {2, 3, 4})
    /\ ~(SUBSET {1, 2} \subseteq SUBSET {2, 3})
    
    \* Integer ranges - negated cases
    /\ ~(SUBSET (0..2) \subseteq SUBSET (0..1))
    /\ ~(SUBSET (0..3) \subseteq SUBSET (1..2))
    /\ ~(SUBSET (0..2) \subseteq SUBSET (1..3))
)

Spec == Init /\ [][Next]_b

TypeInvariant == b \in BOOLEAN

SafetyInvariant == b = TRUE

Invariant == SafetyInvariant /\ TypeInvariant

=============================================================================