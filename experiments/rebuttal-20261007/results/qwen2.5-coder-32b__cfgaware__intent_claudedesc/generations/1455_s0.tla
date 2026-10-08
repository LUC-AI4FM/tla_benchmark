------------------------------- MODULE SubsetOfPowersetTest ------------------------------

CONSTANTS
    \* No constants are needed for this specification

VARIABLES
    testResult

ASSUMPTIONS
    TRUE

DEFINITIONS
    Integers == {-5..5}
    Naturals == {0..5}

Init == testResult' = 
            (SUBSET {1..2} \subseteq SUBSET {1..3}) /\  \* Smaller range is subset of larger range
            ~(SUBSET {1..3} \subseteq SUBSET {1..2}) /\ \* Larger range is not subset of smaller range
            (SUBSET {1..3} \ {2} \subseteq SUBSET {1..3}) /\  \* Removing an element yields a subset
            ~(SUBSET {1..3} \subseteq SUBSET {1..3} \ {2}) /\ \* Original is not subset of removed element
            (SUBSET {} \subseteq SUBSET {}) /\ \* Powerset of empty set is subset of itself
            (SUBSET {} \subseteq SUBSET {1, 2}) /\ \* Powerset of empty set is subset of any powerset
            ~(SUBSET {1, 2} \subseteq SUBSET {}) /\ \* Any non-empty powerset is not subset of empty powerset
            (SUBSET {3} \subseteq SUBSET Integers) /\ \* Powerset of singleton is subset of integers
            (SUBSET {3} \subseteq SUBSET Naturals) /\ \* Powerset of singleton is subset of naturals

Next == TRUE

Spec == Init /\ [][Next]_<<testResult>>

Invariant == testResult \in BOOLEAN /\ testResult = TRUE

THEOREM Spec => [] Invariant

=============================================================================