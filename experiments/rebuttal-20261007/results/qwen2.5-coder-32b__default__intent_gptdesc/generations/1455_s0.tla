------------------------------- MODULE SubsetReasoning -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS 
    MaxInt \* The maximum integer in the range we consider

VARIABLES 
    Sets, \* A set of finite sets of integers
    GlobalConsistency \* Boolean flag indicating global consistency

Init == 
    /\ GlobalConsistency = TRUE
    /\ Sets = {}

Next ==
    \/ \E s1, s2 \in SUBSET (1..MaxInt) : 
        \* Add a subset relationship
        /\ {s1, s2} \notin Sets
        /\ s1 \subseteq s2
        /\ Sets' = Sets \cup {{s1, s2}}
        /\ GlobalConsistency' = GlobalConsistency
    \/ \E s1, s2 \in SUBSET (1..MaxInt) : 
        \* Add a non-subset relationship
        /\ {s1, s2} \notin Sets
        /\ s1 \not\subseteq s2
        /\ Sets' = Sets \cup {{s1, s2}}
        /\ GlobalConsistency' = GlobalConsistency
    \/ GlobalConsistency' = FALSE

Spec == 
    Init /\ [][Next]_<<Sets, GlobalConsistency>>

Invariants ==
    /\ GlobalConsistency \in {TRUE, FALSE}
    /\ \A s1, s2 \in SUBSET (1..MaxInt) : 
        /\ {s1, s2} \in Sets => s1 \subseteq s2
        \/ {s2, s1} \in Sets => s2 \not\subseteq s1

Liveness ==
    \* No additional liveness properties specified in the description

Fairness ==
    WF_next(<<Sets, GlobalConsistency>>)

THEOREM Spec => []Invariants
=============================================================================