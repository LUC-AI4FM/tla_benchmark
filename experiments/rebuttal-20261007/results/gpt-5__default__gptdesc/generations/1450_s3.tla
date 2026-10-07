--------------------------- MODULE RandomFunctionSampler ---------------------------

EXTENDS Integers

(*
  This module samples one function x from a random subset of the function set [S -> T],
  where:
    - S is a finite set of nine integers
    - T is the integer range 1..10

  The full function space [S -> T] has |T|^|S| elements (e.g., 10^9 when |S| = 9),
  which is too large to enumerate explicitly. Instead, x is initialized by choosing
  an element from RandomSubset(1000, [S -> T]). After initialization, the system
  stutters forever. The invariant Inv is trivially TRUE.
*)

CONSTANTS RandomSubset

VARIABLES x

S == {1, 2, 3, 4, 5, 6, 7, 8, 9}
T == 1..10

Init ==
  /\ x \in RandomSubset(1000, [ S -> T ])

Next ==
  UNCHANGED x

Spec ==
  Init /\ [][Next]_x

Inv == TRUE

=============================================================================