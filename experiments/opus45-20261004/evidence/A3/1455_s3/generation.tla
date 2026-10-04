---------------------------- MODULE SubsetRelation ----------------------------
EXTENDS Integers, FiniteSets

VARIABLES b

Init == b = TRUE

Next == b' = (
    \* Positive cases - where SUBSET S \subseteq SUBSET T should hold
    
    \* Empty set is subset of any set's powerset
    /\ (SUBSET {} \subseteq SUBSET {})
    /\ (SUBSET {} \subseteq SUBSET {1, 2, 3})
    
    \* If S \subseteq T then SUBSET S \subseteq SUBSET T
    /\ (SUBSET {1} \subseteq SUBSET {1, 2})
    /\ (SUBSET {1, 2} \subseteq SUBSET {1, 2, 3})
    /\ (SUBSET {2, 3} \subseteq SUBSET {1, 2, 3, 4})
    
    \* Equal sets have equal powersets
    /\ (SUBSET {1, 2} \subseteq SUBSET {1, 2})
    /\ (SUBSET {3, 4, 5} \subseteq SUBSET {3, 4, 5})
    
    \* Integer range subsets
    /\ (SUBSET (1..2) \subseteq SUBSET (1..3))
    /\ (SUBSET (1..3) \subseteq SUBSET (0..4))
    /\ (SUBSET (2..2) \subseteq SUBSET (1..5))
    
    \* Finite sets contained in Nat range
    /\ (SUBSET {0, 1, 2} \subseteq SUBSET (0..10))
    /\ (SUBSET (1..5) \subseteq SUBSET (0..100))
    
    \* Negated cases - where SUBSET S \subseteq SUBSET T should NOT hold
    
    \* Disjoint non-empty sets
    /\ ~(SUBSET {1} \subseteq SUBSET {2})
    /\ ~(SUBSET {1, 2} \subseteq SUBSET {3, 4})
    
    \* S not subset of T means SUBSET S not subset of SUBSET T
    /\ ~(SUBSET {1, 2, 3} \subseteq SUBSET {1, 2})
    /\ ~(SUBSET {1, 2, 3, 4} \subseteq SUBSET {2, 3})
    
    \* Partially overlapping but not contained
    /\ ~(SUBSET {1, 2, 3} \subseteq SUBSET {2, 3, 4})
    /\ ~(SUBSET {0, 1, 2} \subseteq SUBSET {1, 2, 3})
    
    \* Integer ranges where first is not contained in second
    /\ ~(SUBSET (1..5) \subseteq SUBSET (2..4))
    /\ ~(SUBSET (0..10) \subseteq SUBSET (1..9))
    /\ ~(SUBSET (1..3) \subseteq SUBSET (2..5))
    
    \* Single element not in the other set
    /\ ~(SUBSET {5} \subseteq SUBSET {1, 2, 3, 4})
    /\ ~(SUBSET {0} \subseteq SUBSET (1..10))
)

Spec == Init /\ [][Next]_b

TypeInvariant == b \in BOOLEAN

Invariant == b = TRUE /\ b \in BOOLEAN

===============================================================================