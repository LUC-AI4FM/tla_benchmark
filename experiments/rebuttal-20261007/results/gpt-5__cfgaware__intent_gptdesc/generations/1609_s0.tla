----------------------------- MODULE Quicksort -----------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

(*
  High-level nondeterministic Quicksort over a fixed-length array.
  Required bindings: Spec, Termination, ArrayLen
*)

CONSTANT ArrayLen

ASSUME ArrayLen \in Nat

(*
  Finite value domain for array elements. We pick a canonical finite set of integers,
  but the algorithm treats values abstractly via comparisons and multiset preservation.
*)
Val == 0..(ArrayLen - 1)

(*
  Basic interval and range helpers
*)
Intervals ==
  { r \in [lo: 1..ArrayLen, hi: 1..ArrayLen] : r.lo <= r.hi }

LongIntervals ==
  { r \in Intervals : (r.hi - r.lo + 1) >= 2 }

Range(lo, hi) == IF lo <= hi THEN lo..hi ELSE {}

RangeI(I) == Range(I.lo, I.hi)

LenI(lo, hi) == IF lo <= hi THEN (hi - lo + 1) ELSE 0

Isize(I) == I.hi - I.lo

RECURSIVE SetSum(_, _)
SetSum(S, f) ==
  IF S = {} THEN 0
  ELSE
    LET x == CHOOSE e \in S: TRUE
    IN  f[x] + SetSum(S \ {x}, f)

Measure(P) == SetSum(P, Isize)

(*
  Multiset counting inside a subrange and permutation equivalence on a subrange
*)
CountInRange(seq, lo, hi, v) ==
  Cardinality({ i \in Range(lo, hi) : seq[i] = v })

PermutationWithin(A, A2, lo, hi) ==
  \A v \in Val:
    CountInRange(A, lo, hi, v) = CountInRange(A2, lo, hi, v)

SameOutside(A, A2, lo, hi) ==
  \A t \in 1..ArrayLen :
    (t \notin Range(lo, hi)) => A2[t] = A[t]

(*
  Ordering across a partition point p inside [lo..hi]
*)
PartitionOrderOK(A2, lo, hi, p) ==
  /\ lo <= p /\ p <= hi
  /\ \A i \in Range(lo, p - 1), j \in Range(p + 1, hi) : A2[i] <= A2[j]

(*
  Global sortedness
*)
Sorted(A) ==
  \A i, j \in 1..ArrayLen : (i < j) => A[i] <= A[j]

(*
  Variables:
    - A: current array (sequence of length ArrayLen over Val)
    - A0: initial array snapshot (never changes)
    - Pend: finite set of subarray intervals still to process (each of length >= 2)
*)
VARIABLES A, A0, Pend

vars == << A, A0, Pend >>

(*
  Initialization: arbitrary array A over Val of required length,
  A0 records the initial array, and Pend begins with the whole array if it needs sorting.
*)
Init ==
  /\ A \in [1..ArrayLen -> Val]
  /\ A0 = A
  /\ Pend =
       IF ArrayLen >= 2
       THEN { [lo |-> 1, hi |-> ArrayLen] }
       ELSE {}

(*
  One atomic quicksort partition/step on some pending interval I.
  - Chooses a pivot index k in I and a placement position p in I.
  - Produces a rearrangement A2 of A within I that:
      * preserves elements outside I,
      * preserves the multiset of elements within I,
      * puts the chosen pivot value A[k] at position p,
      * ensures every element to the left of p is <= every element to the right of p.
  - Replaces I in Pend by its (up to two) strictly nontrivial subintervals.
  - Decreases the well-founded measure strictly by at least 1.
*)
DoStep ==
  \E I \in Pend,
    p \in RangeI(I),
    k \in RangeI(I),
    A2 \in [1..ArrayLen -> Val] :
    LET L  == [lo |-> I.lo, hi |-> p - 1] IN
    LET R  == [lo |-> p + 1, hi |-> I.hi] IN
    LET addL == (p - I.lo) >= 2 IN
    LET addR == (I.hi - p) >= 2 IN
    LET NewPend ==
         (Pend \ {I})
         \cup (IF addL THEN {L} ELSE {})
         \cup (IF addR THEN {R} ELSE {})
    IN
    /\ SameOutside(A, A2, I.lo, I.hi)
    /\ PermutationWithin(A, A2, I.lo, I.hi)
    /\ A2[p] = A[k]
    /\ PartitionOrderOK(A2, I.lo, I.hi, p)
    /\ A' = A2
    /\ Pend' = NewPend
    /\ A0' = A0
    /\ Measure(NewPend) <= Measure(Pend) - 1

(*
  No further steps needed
*)
Done == Pend = {}

(*
  Type and structural invariants
*)
TypeInv ==
  /\ A \in [1..ArrayLen -> Val]
  /\ A0 \in [1..ArrayLen -> Val]
  /\ Len(A) = ArrayLen
  /\ Len(A0) = ArrayLen
  /\ Pend \subseteq LongIntervals
  /\ \A I, J \in Pend : I # J => (RangeI(I) \cap RangeI(J)) = {}

(*
  Global permutation preservation: A is always a permutation (multiset-equal) of A0
*)
PermutationInv ==
  \A v \in Val : CountInRange(A, 1, ArrayLen, v) = CountInRange(A0, 1, ArrayLen, v)

(*
  Pairs of indices not simultaneously covered by a single pending interval
  must already be in nondecreasing order. This captures the partial order
  established by completed partitions.
*)
CoveredBySame(Ix, Jx) ==
  \E I \in Pend : /\ Ix \in RangeI(I) /\ Jx \in RangeI(I)

PartialOrderInv ==
  \A i, j \in 1..ArrayLen :
    (i < j /\ ~CoveredBySame(i, j)) => A[i] <= A[j]

Inv == TypeInv /\ PermutationInv /\ PartialOrderInv

(*
  Safety: when Done, the array is globally sorted.
  This follows from PartialOrderInv because with Pend = {},
  no pair is covered, so all pairs are ordered.
*)
SafetyWhenDone == Done => Sorted(A)

(*
  Complete behavior: stuttering allowed, with weak fairness on DoStep.
  The measure decreases on every DoStep, proving termination under fairness.
*)
Spec == Init /\ [][DoStep]_vars /\ WF_vars(DoStep)

(*
  Liveness (termination): eventually no further sorting steps are needed.
*)
Termination == <>Done

=============================================================================