---------------------------- MODULE RandomFunctionSampling ----------------------------
\* This module specifies a single-variable system used to sample a random subset
\* of the function set [S -> T], where S is a finite set of nine integers and
\* T is the integer range 1..10.
\*
\* The full function space [S -> T] has 10^9 elements (10 choices for each of
\* 9 elements in S), which should not be explicitly enumerated. Instead, the
\* design initializes x to an element of RandomSubset(1000, [S -> T]).
\*
\* The behavior after initialization is pure stuttering.

EXTENDS Integers, FiniteSets, TLC

CONSTANTS S, T

ASSUME S = {1, 2, 3, 4, 5, 6, 7, 8, 9}
ASSUME T = 1..10

VARIABLES x

\* Initialize x to a randomly chosen function from a random subset of [S -> T]
\* RandomSubset(1000, [S -> T]) returns a random subset of size 1000 from the
\* function space, avoiding explicit enumeration of all 10^9 elements
Init == x \in RandomSubset(1000, [S -> T])

\* After initialization, the system only stutters (no state changes)
Next == UNCHANGED x

\* The complete specification
Spec == Init /\ [][Next]_x

\* Trivial invariant - no substantive safety property
Inv == TRUE

=============================================================================