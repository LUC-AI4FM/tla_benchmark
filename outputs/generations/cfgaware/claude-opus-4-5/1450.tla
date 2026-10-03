---------------------------- MODULE spec ----------------------------

EXTENDS Integers, FiniteSets, TLC

\* S is a finite set of nine integers
\* We use 1..9 as a representative set of nine integers
S == 1..9

\* T is the integer range 1..10
T == 1..10

\* The full function space [S -> T] has 10^9 elements (10 choices for each of 9 elements)
\* This should not be explicitly enumerated, so we use RandomSubset to sample

VARIABLE x

\* Initial state: x is an element of a random subset of [S -> T] with 1000 elements
Init == x \in RandomSubset(1000, [S -> T])

\* The behavior after initialization is pure stuttering
Next == UNCHANGED x

\* The specification
Spec == Init /\ [][Next]_x

\* Trivial invariant
Inv == TRUE

=============================================================================