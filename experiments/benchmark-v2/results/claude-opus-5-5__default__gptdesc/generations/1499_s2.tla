---------------------------- MODULE CoverageStatistics ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N

VARIABLES x, y

vars == <<x, y>>

\* Helper operators referring to variables and primed variables
c == x
d == y'
a == x' = x + 1

Init ==
    /\ x \in 0..3
    /\ y = 0

\* Action using direct primed variables
A ==
    /\ y' = x
    /\ x' = x

\* Action using helper operators c and d
B ==
    /\ d = c
    /\ UNCHANGED x

\* Action using helper a and UNCHANGED over an individual variable
C ==
    /\ x < 3
    /\ a
    /\ UNCHANGED y

\* Action using UNCHANGED over a tuple
D ==
    /\ UNCHANGED <<x, y>>

\* Action using UNCHANGED over vars
E ==
    /\ x > 0
    /\ x' = x - 1
    /\ y' = y

Next == A \/ B \/ C \/ D \/ E

Spec == Init /\ [][Next]_vars

\* Helper operators with quantified expressions over subsets and cardinality
Domain == 0..N

Sum(S) == Cardinality(S)

SmallSubsets == {S \in SUBSET Domain : Cardinality(S) <= 2}

Expensive ==
    \A S \in SUBSET Domain :
        Cardinality(S) <= Cardinality(Domain)

Expensive2 ==
    \E S \in SUBSET Domain :
        /\ Cardinality(S) >= 0
        /\ \A e \in S : e \in Domain

TypeOK ==
    /\ x \in Nat
    /\ y \in Nat

Inv ==
    /\ TypeOK
    /\ x \in 0..3
    /\ y \in 0..3
    /\ Expensive

Inv2 ==
    /\ y <= 3
    /\ Expensive2
    /\ \A S \in SmallSubsets : Cardinality(S) <= 2

THEOREM Spec => []Inv
THEOREM Spec => []Inv2
=============================================================================