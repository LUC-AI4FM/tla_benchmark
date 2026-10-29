---------------------------- MODULE CoverageStatistics ----------------------------
EXTENDS Naturals, FiniteSets

VARIABLES x, y

vars == <<x, y>>

\* Helper operators referring to variables and primed variables
c == x
d == y'
a == x'

Init ==
    /\ x \in 1..3
    /\ y = 0

\* Action using direct primed variables
A ==
    /\ y < 5
    /\ x' = x
    /\ y' = y + 1

\* Action using helper operators c (unprimed) and d (primed)
B ==
    /\ y < 5
    /\ d = y + 1
    /\ x' = c

\* Action using helper operator a and UNCHANGED over an individual variable
C ==
    /\ y < 5
    /\ a = x
    /\ y' = y + 1

\* Action using UNCHANGED over a single variable
D ==
    /\ y < 5
    /\ y' = y + 1
    /\ UNCHANGED x

\* Action using UNCHANGED over a tuple
E ==
    /\ y >= 5
    /\ UNCHANGED <<x, y>>

\* Action using UNCHANGED over vars
F ==
    /\ y >= 5
    /\ UNCHANGED vars

Next ==
    \/ A
    \/ B
    \/ C
    \/ D
    \/ E
    \/ F

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------------

\* Helper operators using quantified expressions over subsets and cardinality
Op1(n) == \A S \in SUBSET (1..n) : Cardinality(S) <= n

Op2(n) == \E S \in SUBSET (1..n) : Cardinality(S) = n

Op3(n) == {S \in SUBSET (1..n) : Cardinality(S) >= 0}

\* State invariants
TypeOK ==
    /\ x \in 1..3
    /\ y \in 0..5

Inv ==
    /\ TypeOK
    /\ Op1(y)
    /\ Op2(x)

Inv2 ==
    /\ Cardinality(Op3(x)) = 2^x
    /\ \A S \in SUBSET (0..y) : Cardinality(S) <= y + 1

===================================================================================