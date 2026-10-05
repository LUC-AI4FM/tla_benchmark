---------------------------- MODULE SubsetRelations ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N, M, K

VARIABLES consistent, step

vars == <<consistent, step>>

Range(a, b) == {i \in Int : a <= i /\ i <= b}

IntSet == Int

NatSet == Nat

EmptySet == {}

Singleton(x) == {x}

RangeSubset(n, m) == (n <= m) => (Range(1, n) \subseteq Range(1, m))

EmptySubsetOfAny(S) == EmptySet \subseteq S

EmptySubsetOfSelf == EmptySet \subseteq EmptySet

SingletonNotSubsetOfEmpty(x) == ~(Singleton(x) \subseteq EmptySet)

FiniteIntSubsetOfInt(S) == IsFiniteSet(S) /\ (\A x \in S : x \in Int) => S \subseteq IntSet

FiniteIntSubsetOfNat(S) == IsFiniteSet(S) /\ (\A x \in S : x \in Nat) => S \subseteq NatSet

LargerRangeNotSubsetOfSmaller(n, m) == (n > m /\ m >= 1) => ~(Range(1, n) \subseteq Range(1, m))

SubsetAssertionsHold ==
    /\ RangeSubset(N, M)
    /\ EmptySubsetOfAny(Range(1, M))
    /\ EmptySubsetOfAny(EmptySet)
    /\ EmptySubsetOfSelf
    /\ SingletonNotSubsetOfEmpty(1)
    /\ SingletonNotSubsetOfEmpty(K)
    /\ FiniteIntSubsetOfInt(Range(1, N))
    /\ FiniteIntSubsetOfNat(Range(1, N))
    /\ LargerRangeNotSubsetOfSmaller(M + 1, M)
    /\ (M > N /\ N >= 1) => ~(Range(1, M) \subseteq Range(1, N))

TypeInvariant ==
    /\ consistent \in BOOLEAN
    /\ step \in Nat

ConsistencyInvariant ==
    /\ consistent = TRUE
    /\ SubsetAssertionsHold

Invariant ==
    /\ TypeInvariant
    /\ ConsistencyInvariant

Init ==
    /\ consistent = TRUE
    /\ step = 0
    /\ SubsetAssertionsHold

MaintainConsistency ==
    /\ SubsetAssertionsHold
    /\ consistent' = TRUE
    /\ step' = step + 1

VerifySubsetRelations ==
    /\ RangeSubset(N, M)
    /\ EmptySubsetOfSelf
    /\ SingletonNotSubsetOfEmpty(1)
    /\ consistent' = consistent
    /\ step' = step + 1

Stutter ==
    /\ UNCHANGED vars

Next ==
    \/ MaintainConsistency
    \/ VerifySubsetRelations
    \/ Stutter

Spec == Init /\ [][Next]_vars

Fairness == WF_vars(MaintainConsistency)

FairSpec == Spec /\ Fairness

ConsistentBoolean == consistent \in BOOLEAN

ConsistentTrue == consistent = TRUE

PreservationProperty == [][SubsetAssertionsHold => SubsetAssertionsHold']_vars

THEOREM Spec => []Invariant

================================================================================