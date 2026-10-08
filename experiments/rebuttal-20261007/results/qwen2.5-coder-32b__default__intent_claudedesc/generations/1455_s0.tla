------------------------------- MODULE SubsetOfPowersetTest -------------------------------

EXTENDS Integers, FiniteSets

CONSTANTS 
    \* No constants needed for this test

VARIABLES 
    testResult

Init == testResult = TRUE /\ 
        (SUBSET {1..2}) \subseteq (SUBSET {1..3}) /\ 
        ~(SUBSET {1..3}) \subseteq (SUBSET {1..2}) /\ 
        (SUBSET {1..3} \ {2}) \subseteq (SUBSET {1..3}) /\ 
        ~(SUBSET {1..3}) \subseteq (SUBSET {1..3} \ {2}) /\ 
        ({1} \subseteq {1, 2}) => ((SUBSET {1}) \subseteq (SUBSET {1, 2})) /\ 
        {} \in (SUBSET {}) /\ 
        (SUBSET {}) \subseteq (SUBSET {1}) /\ 
        ~(SUBSET {1}) \subseteq (SUBSET {}) /\ 
        (SUBSET {0}) \subseteq (SUBSET Int) /\ 
        (SUBSET {0}) \subseteq (SUBSET Nat)

Next == TRUE

Spec == Init /\ [][Next]_<<testResult>>

Invariant == testResult \in BOOLEAN /\ testResult = TRUE

=============================================================================