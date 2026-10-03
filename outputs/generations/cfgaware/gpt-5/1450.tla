------------------------------ MODULE RandomFunctionSampler ------------------------------

EXTENDS Integers, FiniteSets

(*
  This module specifies a single-variable system used to sample a random subset
  of the function set [S -> T], where:
    - S is a finite set of nine integers, and
    - T is the integer range 1..10.
  The full function space [S -> T] has 10^8 elements and should not be explicitly
  enumerated. Instead, x is initialized to an element of RandomSubset(1000, [S -> T]).
  After initialization, the behavior is pure stuttering. A trivial invariant Inv == TRUE
  is included.
*)

(******************************************************************
  Basic sets
******************************************************************)
S == 1..9
T == 1..10

(******************************************************************
  Utilities
******************************************************************)
Min(a, b) == IF a <= b THEN a ELSE b

(*
  RandomSubset(k, U) nondeterministically returns some subset of U whose
  size is Min(k, Cardinality(U)).
*)
RandomSubset(k, U) ==
  CHOOSE SS \in SUBSET U : Cardinality(SS) = Min(k, Cardinality(U))

(******************************************************************
  State and behavior
******************************************************************)
VARIABLES x

Init ==
  LET FSet == [ S -> T ] IN
  LET RS == RandomSubset(1000, FSet) IN
  x \in RS

Next == UNCHANGED x

Spec == Init /\ [][Next]_x

(******************************************************************
  Trivial invariant
******************************************************************)
Inv == TRUE

=============================================================================