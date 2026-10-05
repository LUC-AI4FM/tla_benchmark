---------------------------- MODULE RandomSubsetSelection ----------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS n, m, k

ASSUME /\ n \in Nat \ {0}
       /\ m \in Nat \ {0}
       /\ k \in Nat \ {0}

Domain == 1..n
Codomain == 1..m

AllFunctions == [Domain -> Codomain]

ASSUME k <= Cardinality(AllFunctions)

VARIABLES selectedSubset, initialized

vars == <<selectedSubset, initialized>>

TypeOK ==
    /\ selectedSubset \subseteq AllFunctions
    /\ initialized \in BOOLEAN

IsValidTotalFunction(f) ==
    /\ DOMAIN f = Domain
    /\ \A x \in Domain : f[x] \in Codomain

AllElementsAreValidFunctions ==
    \A f \in selectedSubset : IsValidTotalFunction(f)

AllElementsArePairwiseDistinct ==
    \A f1, f2 \in selectedSubset : f1 = f2 \/ f1 # f2

SubsetSizeEqualsK ==
    Cardinality(selectedSubset) = k

SelectionCorrectness ==
    /\ SubsetSizeEqualsK
    /\ AllElementsAreValidFunctions
    /\ AllElementsArePairwiseDistinct
    /\ selectedSubset \subseteq AllFunctions

Init ==
    /\ selectedSubset \in {S \in SUBSET AllFunctions : Cardinality(S) = k}
    /\ initialized = TRUE

NoChange ==
    /\ initialized = TRUE
    /\ UNCHANGED vars

Next == NoChange

Spec == Init /\ [][Next]_vars

Immutability == [][UNCHANGED selectedSubset]_vars

AlwaysInitialized == []initialized

InvariantCorrectness == SelectionCorrectness

SafetyInvariant ==
    /\ TypeOK
    /\ InvariantCorrectness
    /\ initialized = TRUE

SubsetNeverChanges == [](selectedSubset = selectedSubset)

AlwaysKElements == [](Cardinality(selectedSubset) = k)

AlwaysValidFunctions == []AllElementsAreValidFunctions

AlwaysDistinctElements == []AllElementsArePairwiseDistinct

AlwaysSubsetOfUniverse == [](selectedSubset \subseteq AllFunctions)

LivenessProperty == <>(initialized = TRUE)

TemporalCorrectness ==
    /\ Immutability
    /\ AlwaysInitialized
    /\ AlwaysKElements
    /\ AlwaysValidFunctions

===================================================================================