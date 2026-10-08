------------------------------- MODULE SubsetReasoning -------------------------------

CONSTANTS 
    \* Constants for defining ranges and sets
    Integers, NaturalNumbers,
    \* Example constants for testing specific cases
    n, m

VARIABLES 
    \* Variable to represent the global consistency flag
    Consistent

\* Define finite set of integers from 1 to k
FiniteRange(k) == {i \in Integers : 1 <= i /\ i <= k}

\* Define initial state where consistency is true
Init == 
    /\ Consistent = TRUE

\* Next-state relation that preserves the consistency flag and subset relationships
Next ==
    /\ \/ CHOOSE s1, s2 \in SUBSET Integers: s1 \subseteq s2
       \/ CHOOSE s1, s2 \in SUBSET Integers: ~(s1 \subseteq s2)
    /\ Consistent' = (Consistent /\ 
        (\A s1, s2 \in SUBSET Integers: (s1 \subseteq s2) => (s1' \subseteq s2')) /\
        (\A s1, s2 \in SUBSET Integers: ~(s1 \subseteq s2) => ~(s1' \subseteq s2')))

\* Specification of the system
Spec == 
    Init /\ [][Next]_<<Consistent>>

\* Invariants to be checked
TypeOK ==
    /\ Consistent \in BOOLEAN

SubsetProperties ==
    /\ {} \subseteq {}
    /\ (\A k \in NaturalNumbers: FiniteRange(k) \subseteq Integers)
    /\ (\A k \in NaturalNumbers: FiniteRange(k) \subseteq NaturalNumbers)
    /\ (\A k \in NaturalNumbers: k <= m => FiniteRange(k) \subseteq FiniteRange(m))
    /\ (\A k \in NaturalNumbers: {k} \not\subseteq {})

Invariant ==
    TypeOK /\ SubsetProperties

THEOREM Spec => []Invariant

=============================================================================