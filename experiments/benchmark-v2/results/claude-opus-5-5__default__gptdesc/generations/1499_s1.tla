---------------------------- MODULE CoverageStatistics ----------------------------
EXTENDS Naturals, FiniteSets

VARIABLES x, y

vars == <<x, y>>

\* Helper operators referring to variables and primed variables
c == x
d == x'
a(n) == y' = n

Init == /\ x = 1
        /\ y = 1

\* Direct reference to variables, UNCHANGED over a single variable
A1 == /\ x < 5
      /\ x' = x + 1
      /\ UNCHANGED y

\* Reference to x through helper operator c
A2 == /\ c < 5
      /\ x' = c + 1
      /\ UNCHANGED <<y>>

\* Primed y set through helper operator a
A3 == /\ y < 5
      /\ a(y + 1)
      /\ UNCHANGED x

\* Primed x referred to through helper operator d
A4 == /\ x > 1
      /\ d = x - 1
      /\ y' = y

\* Reset using both helpers
A5 == /\ x = 5
      /\ y = 5
      /\ d = 1
      /\ a(1)

\* Explicit stuttering via UNCHANGED over a tuple
A6 == UNCHANGED <<x, y>>

\* Stuttering via UNCHANGED over the vars tuple
A7 == UNCHANGED vars

Next == \/ A1
        \/ A2
        \/ A3
        \/ A4
        \/ A5
        \/ A6
        \/ A7

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* Helper operators with quantification over subsets and cardinality
AllSubsetsSmaller(S) == \A T \in SUBSET S : Cardinality(T) <= Cardinality(S)

ExistsSubsetOfSize(S, k) == \E T \in SUBSET S : Cardinality(T) = k

TypeOK == /\ x \in 1..5
          /\ y \in 1..5

Inv == /\ TypeOK
       /\ AllSubsetsSmaller(1..x)
       /\ AllSubsetsSmaller(1..y)

Inv2 == /\ ExistsSubsetOfSize(1..x, x)
        /\ ExistsSubsetOfSize(1..y, y)
        /\ \A T \in SUBSET (1..x) : \A U \in SUBSET T :
               Cardinality(U) <= Cardinality(T)

=============================================================================