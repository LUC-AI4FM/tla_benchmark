---------------------------- MODULE SubsetRelations ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS
    MaxInt,         \* Upper bound for integer ranges
    ArbitrarySets   \* A set of arbitrary finite sets to reason about

VARIABLES
    subsetFacts,    \* Set of pairs (A, B) where A \subseteq B is asserted
    nonSubsetFacts, \* Set of pairs (A, B) where A \subseteq B is denied
    consistent      \* Boolean flag witnessing global consistency

vars == <<subsetFacts, nonSubsetFacts, consistent>>

-----------------------------------------------------------------------------
(* Helper definitions for set representations *)

\* Range of integers from 1 to n
Range(n) == IF n < 1 THEN {} ELSE 1..n

\* Extended range including zero (natural numbers up to n)
NatRange(n) == IF n < 0 THEN {} ELSE 0..n

\* The set of all integers we consider (bounded by MaxInt)
AllIntegers == -MaxInt..MaxInt

\* The set of natural numbers we consider (bounded by MaxInt)
AllNaturals == 0..MaxInt

\* Empty set
EmptySet == {}

\* Singleton set
Singleton(x) == {x}

-----------------------------------------------------------------------------
(* Core subset relation evaluation *)

\* Evaluate whether set A is actually a subset of set B
IsSubset(A, B) == A \subseteq B

\* Check if the subset fact (A, B) is logically valid
ValidSubsetFact(A, B) == IsSubset(A, B)

\* Check if the non-subset fact (A, B) is logically valid
ValidNonSubsetFact(A, B) == ~IsSubset(A, B)

-----------------------------------------------------------------------------
(* Consistency checking *)

\* All asserted subset facts are actually true
SubsetFactsConsistent(sf) ==
    \A fact \in sf : ValidSubsetFact(fact[1], fact[2])

\* All asserted non-subset facts are actually true
NonSubsetFactsConsistent(nsf) ==
    \A fact \in nsf : ValidNonSubsetFact(fact[1], fact[2])

\* No contradictions: nothing asserted as both subset and non-subset
NoContradictions(sf, nsf) ==
    sf \cap nsf = {}

\* Overall consistency predicate
IsConsistent(sf, nsf) ==
    /\ SubsetFactsConsistent(sf)
    /\ NonSubsetFactsConsistent(nsf)
    /\ NoContradictions(sf, nsf)

-----------------------------------------------------------------------------
(* Fundamental subset facts that must always hold *)

\* Range(n) \subseteq Range(m) when n <= m
RangeSubsetFacts ==
    { <<Range(n), Range(m)>> : n, m \in 0..MaxInt, n <= m }

\* Empty set is subset of any set including itself
EmptySubsetFacts ==
    { <<EmptySet, Range(n)>> : n \in 0..MaxInt } \cup
    { <<EmptySet, NatRange(n)>> : n \in -1..MaxInt } \cup
    { <<EmptySet, EmptySet>> } \cup
    { <<EmptySet, AllIntegers>> } \cup
    { <<EmptySet, AllNaturals>> }

\* Finite sets of integers are subsets of AllIntegers and AllNaturals (when non-negative)
FiniteIntSubsetFacts ==
    { <<Range(n), AllIntegers>> : n \in 0..MaxInt } \cup
    { <<Range(n), AllNaturals>> : n \in 0..MaxInt } \cup
    { <<NatRange(n), AllIntegers>> : n \in -1..MaxInt } \cup
    { <<NatRange(n), AllNaturals>> : n \in -1..MaxInt }

\* Core true subset facts
CoreSubsetFacts ==
    RangeSubsetFacts \cup EmptySubsetFacts \cup FiniteIntSubsetFacts

\* Singleton is not a subset of empty set
SingletonNonSubsetFacts ==
    { <<Singleton(x), EmptySet>> : x \in -MaxInt..MaxInt }

\* Larger range is not subset of smaller range (when n > m and m >= 0)
RangeNonSubsetFacts ==
    { <<Range(n), Range(m)>> : n, m \in 1..MaxInt, n > m }

\* Core non-subset facts
CoreNonSubsetFacts ==
    SingletonNonSubsetFacts \cup RangeNonSubsetFacts

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ subsetFacts = CoreSubsetFacts
    /\ nonSubsetFacts = CoreNonSubsetFacts
    /\ consistent = IsConsistent(CoreSubsetFacts, CoreNonSubsetFacts)

-----------------------------------------------------------------------------
(* Actions *)

\* Add a new valid subset fact
AddSubsetFact(A, B) ==
    /\ ValidSubsetFact(A, B)
    /\ <<A, B>> \notin subsetFacts
    /\ <<A, B>> \notin nonSubsetFacts
    /\ subsetFacts' = subsetFacts \cup {<<A, B>>}
    /\ nonSubsetFacts' = nonSubsetFacts
    /\ consistent' = IsConsistent(subsetFacts', nonSubsetFacts')

\* Add a new valid non-subset fact
AddNonSubsetFact(A, B) ==
    /\ ValidNonSubsetFact(A, B)
    /\ <<A, B>> \notin nonSubsetFacts
    /\ <<A, B>> \notin subsetFacts
    /\ nonSubsetFacts' = nonSubsetFacts \cup {<<A, B>>}
    /\ subsetFacts' = subsetFacts
    /\ consistent' = IsConsistent(subsetFacts', nonSubsetFacts')

\* Derive a transitive subset fact: if A \subseteq B and B \subseteq C then A \subseteq C
DeriveTransitiveSubset ==
    \E fact1, fact2 \in subsetFacts :
        /\ fact1[2] = fact2[1]
        /\ <<fact1[1], fact2[2]>> \notin subsetFacts
        /\ ValidSubsetFact(fact1[1], fact2[2])
        /\ subsetFacts' = subsetFacts \cup {<<fact1[1], fact2[2]>>}
        /\ nonSubsetFacts' = nonSubsetFacts
        /\ consistent' = IsConsistent(subsetFacts', nonSubsetFacts')

\* Stutter step - system can remain idle
Stutter ==
    /\ subsetFacts' = subsetFacts
    /\ nonSubsetFacts' = nonSubsetFacts
    /\ consistent' = consistent

\* All possible sets we reason about
AllSets ==
    { Range(n) : n \in 0..MaxInt } \cup
    { NatRange(n) : n \in -1..MaxInt } \cup
    { Singleton(x) : x \in -MaxInt..MaxInt } \cup
    { EmptySet, AllIntegers, AllNaturals } \cup
    ArbitrarySets

Next ==
    \/ \E A, B \in AllSets : AddSubsetFact(A, B)
    \/ \E A, B \in AllSets : AddNonSubsetFact(A, B)
    \/ DeriveTransitiveSubset
    \/ Stutter

-----------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety Invariants *)

\* The consistent flag is always a boolean
TypeInvariant ==
    /\ consistent \in BOOLEAN
    /\ subsetFacts \subseteq (SUBSET AllIntegers) \times (SUBSET AllIntegers)
    /\ nonSubsetFacts \subseteq (SUBSET AllIntegers) \times (SUBSET AllIntegers)

\* The consistent flag is always TRUE
ConsistencyInvariant ==
    consistent = TRUE

\* All subset assertions are logically correct
SubsetCorrectnessInvariant ==
    \A fact \in subsetFacts : fact[1] \subseteq fact[2]

\* All non-subset assertions are logically correct
NonSubsetCorrectnessInvariant ==
    \A fact \in nonSubsetFacts : ~(fact[1] \subseteq fact[2])

\* No contradictions exist in the knowledge base
NoContradictionInvariant ==
    subsetFacts \cap nonSubsetFacts = {}

\* Core mathematical truths are preserved
\* Range(n) \subseteq Range(m) when n <= m
RangeMonotonicityInvariant ==
    \A n, m \in 0..MaxInt : n <= m => <<Range(n), Range(m)>> \in subsetFacts

\* Empty set is always a subset of itself and any range
EmptySetInvariant ==
    /\ <<EmptySet, EmptySet>> \in subsetFacts
    /\ \A n \in 0..MaxInt : <<EmptySet, Range(n)>> \in subsetFacts

\* Singleton non-subset of empty set
SingletonInvariant ==
    \A x \in -MaxInt..MaxInt : <<Singleton(x), EmptySet>> \in nonSubsetFacts

\* Combined safety invariant
SafetyInvariant ==
    /\ TypeInvariant
    /\ ConsistencyInvariant
    /\ SubsetCorrectnessInvariant
    /\ NonSubsetCorrectnessInvariant
    /\ NoContradictionInvariant

-----------------------------------------------------------------------------
(* Liveness Properties *)

\* The system maintains consistency forever
AlwaysConsistent == []ConsistencyInvariant

\* Once a subset fact is established, it remains true forever
SubsetFactsPersist ==
    \A A, B \in AllSets : 
        [](<<A, B>> \in subsetFacts => [](<<A, B>> \in subsetFacts))

\* Once a non-subset fact is established, it remains true forever
NonSubsetFactsPersist ==
    \A A, B \in AllSets :
        [](<<A, B>> \in nonSubsetFacts => [](<<A, B>> \in nonSubsetFacts))

\* Facts are preserved over all transitions
FactPreservation ==
    /\ [](subsetFacts \subseteq subsetFacts')
    /\ [](nonSubsetFacts \subseteq nonSubsetFacts')

=============================================================================