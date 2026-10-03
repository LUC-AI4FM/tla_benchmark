------------------------------ MODULE RandomSample ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS S, T, N

(*--------------------------------------------------------------------
  The configuration must bind the following constants:
      - S : a finite set of nine integers (e.g., {1,2,…,9})
      - T : the integer range 1..10
      - N : the size of the random subset to be sampled (here 1000)
--------------------------------------------------------------------*)

VARIABLE x

(*--------------------------------------------------------------------
  RandomSubset(k, F) is a placeholder for a nondeterministic choice of
  k distinct elements from the set F.  For the purposes of this
  specification we simply allow any element of F; the cardinality
  constraint is not enforced explicitly.
--------------------------------------------------------------------*)
RandomSubset(k, F) == { f \in F : TRUE }

(*--------------------------------------------------------------------
  Initial state: x is chosen nondeterministically from a random subset
  of size N of the function space [S -> T].
--------------------------------------------------------------------*)
Init == x \in RandomSubset(N, [S -> T])

(*--------------------------------------------------------------------
  After initialization the system stutters; x never changes.
--------------------------------------------------------------------*)
Next == /\ x' = x

(*--------------------------------------------------------------------
  Trivial invariant (always true).
--------------------------------------------------------------------*)
Inv == TRUE

Spec == Init /\ [][Next]_x
=============================================================================