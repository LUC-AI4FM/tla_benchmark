---------------------------- MODULE RandomFunctionSubset ----------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS n, m, k

ASSUME n \in Nat /\ n > 0
ASSUME m \in Nat /\ m > 0
ASSUME k \in Nat /\ k > 0

Domain == 1..n
Codomain == 1..m

AllFunctions == [Domain -> Codomain]

VARIABLE selectedSubset
VARIABLE initialized

vars == <<selectedSubset, initialized>>

TypeOK ==
    /\ selectedSubset \subseteq AllFunctions
    /\ initialized \in BOOLEAN

IsValidFunction(f) ==
    /\ DOMAIN f = Domain
    /\ \A x \in Domain : f[x] \in Codomain

AllDistinct(S) ==
    \A f1, f2 \in S : f1 = f2 \/ f1 # f2

SubsetSizeEqualsK ==
    Cardinality(selectedSubset) = k

AllElementsAreValidFunctions ==
    \A f \in selectedSubset : IsValidFunction(f)

AllElementsPairwiseDistinct ==
    \A f1, f2 \in selectedSubset : f1 # f2 => f1 # f2

SelectionCorrectness ==
    /\ SubsetSizeEqualsK
    /\ AllElementsAreValidFunctions
    /\ AllElementsPairwiseDistinct

Init ==
    /\ initialized = FALSE
    /\ selectedSubset = {}

SelectRandomSubset ==
    /\ initialized = FALSE
    /\ \E S \in SUBSET AllFunctions :
        /\ Cardinality(S) = k
        /\ selectedSubset' = S
        /\ initialized' = TRUE

Stutter ==
    /\ initialized = TRUE
    /\ UNCHANGED vars

Next ==
    \/ SelectRandomSubset
    \/ Stutter

Spec == Init /\ [][Next]_vars /\ WF_vars(SelectRandomSubset)

Immutability ==
    [][initialized => selectedSubset' = selectedSubset]_vars

ImmutabilityTemporal ==
    [](initialized => [](selectedSubset = selectedSubset))

EventuallyInitialized ==
    <>(initialized)

AlwaysCorrectAfterInit ==
    [](initialized => SelectionCorrectness)

SafetyInvariant ==
    initialized => SelectionCorrectness

TypeInvariant ==
    /\ TypeOK
    /\ (initialized => SelectionCorrectness)

Liveness == EventuallyInitialized

THEOREM Spec => []TypeInvariant
THEOREM Spec => []SafetyInvariant
THEOREM Spec => Immutability
THEOREM Spec => AlwaysCorrectAfterInit
THEOREM Spec => Liveness

=============================================================================