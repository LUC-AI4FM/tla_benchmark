------------------------------ MODULE SampleRandomFunc ------------------------------

(*
  This module models sampling a single function x from a random subset of the function
  space [S -> T], where:
    - S is a finite set of nine integers,
    - T is the integer range 1..10.

  The full function space [S -> T] has size 10^|S| (e.g., 10^8 when |S| = 8),
  which should not be explicitly enumerated. Instead, initialization chooses x
  from a subset returned by RandomSubset(1000, [S -> T]). After initialization,
  the behavior is pure stuttering. A trivial invariant Inv == TRUE is included.
*)

EXTENDS Integers, FiniteSets

CONSTANT S
CONSTANT RandomSubset(_, _)

(*
  S is a finite set of nine integers.
*)
ASSUME /\ S \subseteq Int
       /\ Cardinality(S) = 9

T == 1..10
FuncSpace == [S -> T]

(*
  Assumptions constraining the abstract RandomSubset operator for the specific
  use in this module. It returns a nonempty subset of FuncSpace with size at most 1000.
*)
ASSUME /\ RandomSubset(1000, FuncSpace) \subseteq FuncSpace
       /\ RandomSubset(1000, FuncSpace) # {}
       /\ Cardinality(RandomSubset(1000, FuncSpace)) <= 1000

VARIABLE x

Init == x \in RandomSubset(1000, FuncSpace)

Next == UNCHANGED x

Spec == Init /\ [][Next]_x

Inv == TRUE

=============================================================================