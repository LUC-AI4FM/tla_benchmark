------------------------------ MODULE RandomFunctionSampler ------------------------------

EXTENDS Naturals, FiniteSets

\* This module models sampling from a huge function space without enumerating it.
\* S is a finite set of nine integers; T is the integer range 1..10.
\* The full function space [S -> T] would have 10^8 elements (per comment) and should
\* not be explicitly enumerated. We instead select x from a subset of size at most 1000.
\* After initialization, the behavior is pure stuttering.
\* The invariant is the trivial Inv == TRUE.

S == 1..9
T == 1..10
K == 1000

\* A nondeterministic choice of a nonempty subset of U with size at most k.
RandomSubset(k, U) ==
  CHOOSE B \in SUBSET U : B # {} /\ Cardinality(B) <= k

VARIABLES x

vars == << x >>

Init ==
  \* Pick x from some nonempty subset of [S -> T] of size at most K.
  LET RS == RandomSubset(K, [S -> T])
  IN x \in RS

Next ==
  UNCHANGED vars

Spec ==
  Init /\ [][Next]_vars

Inv ==
  TRUE

=============================================================================