---------------------------- MODULE SubsetOfPowerset ----------------------------
EXTENDS Integers, FiniteSets

VARIABLES result

\* Test cases for subset-of-powerset behavior

\* Test 1: Powerset of smaller range is subset of powerset of larger range
Test1 == (SUBSET (1..2)) \subseteq (SUBSET (1..3))

\* Test 2: Powerset of larger range is NOT subset of powerset of smaller range
Test2 == ~((SUBSET (1..3)) \subseteq (SUBSET (1..2)))

\* Test 3: Removing an element yields powerset that is subset of original
Test3 == (SUBSET (2..3)) \subseteq (SUBSET (1..3))

\* Test 4: Original powerset is NOT subset of reduced powerset
Test4 == ~((SUBSET (1..3)) \subseteq (SUBSET (2..3)))

\* Test 5: Nested set inclusions with small explicit sets
Test5 == (SUBSET {1}) \subseteq (SUBSET {1, 2})

\* Test 6: Nested inclusion - larger not subset of smaller
Test6 == ~((SUBSET {1, 2}) \subseteq (SUBSET {1}))

\* Test 7: Powerset of empty set is subset of itself
Test7 == (SUBSET {}) \subseteq (SUBSET {})

\* Test 8: Powerset of empty set is subset of any other powerset
Test8 == (SUBSET {}) \subseteq (SUBSET {1, 2, 3})

\* Test 9: Non-empty powerset is NOT subset of powerset of empty set
Test9 == ~((SUBSET {1}) \subseteq (SUBSET {}))

\* Test 10: Powerset of singleton is subset of powerset of larger set containing it
Test10 == (SUBSET {0}) \subseteq (SUBSET (0..5))

\* Test 11: Powerset of singleton is subset of powerset containing natural numbers (small sample)
Test11 == (SUBSET {1}) \subseteq (SUBSET (0..10))

\* Test 12: Empty set's powerset {{}} is subset of any powerset
Test12 == (SUBSET {}) \subseteq (SUBSET {42})

\* Test 13: Disjoint sets - neither powerset is subset of the other
Test13 == ~((SUBSET {1, 2}) \subseteq (SUBSET {3, 4}))

\* Test 14: Equal sets have equal powersets (subset in both directions)
Test14 == ((SUBSET {1, 2}) \subseteq (SUBSET {1, 2})) /\ ((SUBSET {1, 2}) \subseteq (SUBSET {1, 2}))

\* Test 15: Proper subset relation for explicit integer sets
Test15 == (SUBSET {5}) \subseteq (SUBSET {5, 6, 7})

\* Conjunction of all test cases
AllTests == Test1 /\ Test2 /\ Test3 /\ Test4 /\ Test5 /\ Test6 /\ Test7 /\ 
            Test8 /\ Test9 /\ Test10 /\ Test11 /\ Test12 /\ Test13 /\ Test14 /\ Test15

Init == result = AllTests

Next == result' = result

Spec == Init /\ [][Next]_result

\* Safety invariant: result remains TRUE and is a member of BOOLEAN
TypeInvariant == result \in BOOLEAN

CorrectBehavior == result = TRUE

Invariant == TypeInvariant /\ CorrectBehavior

=============================================================================