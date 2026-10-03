---------------------------- MODULE RandomFunctionSubset ----------------------------
\* This module specifies a single-variable system used to sample a random subset
\* of the function set [S -> T], where S is a finite set of nine integers and T
\* is the integer range 1..10.
\*
\* The full function space [S -> T] has 10^9 elements (10 choices for each of 9
\* elements in S), which should not be explicitly enumerated. Instead, the design
\* initializes x to an element of RandomSubset(1000, [S -> T]), which samples
\* 1000 random functions from the space without enumerating all possibilities.
\*
\* The behavior after initialization is pure stuttering.

EXTENDS Integers, FiniteSets, TLC

CONSTANTS S, T

ASSUME S = {1, 2, 3, 4, 5, 6, 7, 8, 9}
ASSUME T = 1..10

VARIABLES x

\* Initialize x to a randomly selected function from the function space [S -> T].
\* RandomSubset(1000, [S -> T]) returns a set of 1000 randomly chosen functions,
\* and we pick one element from that set.
Init == x \in RandomSubset(1000, [S -> T])

\* The behavior after initialization is pure stuttering (no state changes).
Next == UNCHANGED x

\* The trivial invariant - no substantive safety property is specified.
Inv == TRUE

\* The complete specification with stuttering steps allowed.
Spec == Init /\ [][Next]_x

===================================================================================