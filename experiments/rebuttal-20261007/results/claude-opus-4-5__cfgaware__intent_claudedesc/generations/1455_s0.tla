---------------------------- MODULE SubsetPowerset ----------------------------
EXTENDS Integers, FiniteSets

VARIABLES result

\* Test case 1: Powerset of smaller range is subset of powerset of larger range
TestSmallerSubsetLarger == SUBSET (1..2) \subseteq SUBSET (1..3)
TestLargerNotSubsetSmaller == ~(SUBSET (1..3) \subseteq SUBSET (1..2))

\* Test case 2: Removing an element yields a powerset that is subset of original
TestRemovedSubsetOriginal == SUBSET (2..3) \subseteq SUBSET (1..3)
TestOriginalNotSubsetRemoved == ~(SUBSET (1..3) \subseteq SUBSET (2..3))

\* Test case 3: Nested set inclusions for small explicit sets
TestNestedSmall1 == SUBSET {1} \subseteq SUBSET {1, 2}
TestNestedSmall2 == SUBSET {1, 2} \subseteq SUBSET {1, 2, 3}
TestNestedSmall3 == ~(SUBSET {1, 2, 3} \subseteq SUBSET {1, 2})

\* Test case 4: Empty set powerset properties
TestEmptySubsetSelf == SUBSET {} \subseteq SUBSET {}
TestEmptySubsetAny == SUBSET {} \subseteq SUBSET {1, 2, 3}
TestAnyNotSubsetEmpty == ~(SUBSET {1} \subseteq SUBSET {})

\* Test case 5: Singleton powerset is subset of larger powersets
TestSingletonSubsetRange == SUBSET {0} \subseteq SUBSET (0..5)
TestSingletonSubsetNats == SUBSET {1} \subseteq SUBSET (1..10)

\* Combined result of all test cases
AllTests == /\ TestSmallerSubsetLarger
            /\ TestLargerNotSubsetSmaller
            /\ TestRemovedSubsetOriginal
            /\ TestOriginalNotSubsetRemoved
            /\ TestNestedSmall1
            /\ TestNestedSmall2
            /\ TestNestedSmall3
            /\ TestEmptySubsetSelf
            /\ TestEmptySubsetAny
            /\ TestAnyNotSubsetEmpty
            /\ TestSingletonSubsetRange
            /\ TestSingletonSubsetNats

Init == result = AllTests

Next == result' = result

Spec == Init /\ [][Next]_result

TypeInvariant == result \in BOOLEAN

Inv == result = TRUE /\ result \in BOOLEAN

=============================================================================