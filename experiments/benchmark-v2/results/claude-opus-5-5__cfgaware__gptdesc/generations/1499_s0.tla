---------------------------- MODULE CostInvariants ----------------------------
EXTENDS Naturals, FiniteSets

VARIABLES x, y

vars == <<x, y>>

\* Helper operators referring to variables and primed variables
c == x
d == x'
a == y' = y

Init ==
    /\ x = 0
    /\ y = 0

\* Increment x directly, leave y unchanged
A1 ==
    /\ x' = x + 1
    /\ UNCHANGED y

\* Increment x through the helper operators c, d and a
A2 ==
    /\ d = c + 1
    /\ a

\* Increment y, leave x unchanged (tuple form)
A3 ==
    /\ y' = y + 1
    /\ UNCHANGED <<x>>

\* Increment both variables
A4 ==
    /\ x' = c + 1
    /\ y' = y + 1

\* Stuttering step over the whole tuple
A5 ==
    UNCHANGED <<x, y>>

Next == A1 \/ A2 \/ A3 \/ A4 \/ A5

Spec == Init /\ [][Next]_vars

\* State constraint to bound the state space
Constraint ==
    /\ x <= 4
    /\ y <= 4

\* Helper operators using quantification over subsets and cardinality
SubsetsOf(n) == SUBSET (0..n)

AllSubsetsBounded(n) ==
    \A S \in SubsetsOf(n) : Cardinality(S) <= n + 1

ExistsSubsetOfSize(n, k) ==
    \E S \in SubsetsOf(n) : Cardinality(S) = k

Inv ==
    /\ x \in Nat
    /\ y \in Nat
    /\ AllSubsetsBounded(x)

Inv2 ==
    /\ \A k \in 0..(y + 1) : ExistsSubsetOfSize(y, k)
    /\ Cardinality(SubsetsOf(x)) = 2^(x + 1)

=============================================================================