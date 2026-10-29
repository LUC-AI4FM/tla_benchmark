------------------------- MODULE NondetQuickSort -------------------------
(***************************************************************************)
(* Non-deterministic in-place quicksort over an abstract array.            *)
(*                                                                         *)
(* Domain: the array is a finite sequence of length N whose elements are   *)
(* drawn from a finite, totally ordered set Values. Values is a subset of  *)
(* Int, so the total order is the standard <=.                             *)
(*                                                                         *)
(* The work set "pending" is a set of index intervals <<lo, hi>>. The      *)
(* pending intervals are always pairwise disjoint, so a set is sufficient  *)
(* and a multiset is not needed. A partition step may choose any pivot p   *)
(* with lo <= p < hi. It may also produce any rearrangement of the         *)
(* interval that:                                                          *)
(*   - is a permutation of the original contents,                          *)
(*   - leaves every index outside the interval unchanged, and              *)
(*   - places only elements <= the right part into [lo, p].                *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    N,        \* number of array elements
    Values    \* finite totally ordered domain of element values

ASSUME NAssump      == N \in Nat
ASSUME ValuesAssump == /\ Values \subseteq Int
                       /\ Values # {}
                       /\ IsFiniteSet(Values)

VARIABLES
    arr,      \* the current array, a sequence of length N
    arr0,     \* ghost variable: the original array, used for specification
    pending   \* set of pending intervals <<lo, hi>>

vars == <<arr, arr0, pending>>

Idx       == 1..N
ArrayType == [Idx -> Values]
Interval  == (1..N) \X (0..N)   \* <<lo, hi>> pairs

-----------------------------------------------------------------------------
(* Helper operators *)

Count(s, v) == Cardinality({i \in DOMAIN s : s[i] = v})

\* a and b contain the same multiset of values
IsPerm(a, b) == \A v \in Values : Count(a, v) = Count(b, v)

\* a and b agree on every index outside [lo, hi]
SameOutside(a, b, lo, hi) == \A k \in Idx : (k < lo \/ k > hi) => a[k] = b[k]

\* every element of [lo, p] is <= every element of [p+1, hi]
SplitOrdered(b, lo, p, hi) ==
    \A i \in lo..p : \A j \in (p+1)..hi : b[i] <= b[j]

Sorted(a) == \A i, j \in Idx : i < j => a[i] <= a[j]

InInterval(i, iv) == iv[1] <= i /\ i <= iv[2]

\* Every legal outcome of a partition step on [lo, hi] with pivot p.
\* This set is never empty, because sorting the interval satisfies all
\* three constraints.
PartitionResults(a, lo, p, hi) ==
    { b \in ArrayType :
        /\ SameOutside(a, b, lo, hi)  \* elements outside are preserved
        /\ IsPerm(a, b)               \* with SameOutside, only [lo,hi] is permuted
        /\ SplitOrdered(b, lo, p, hi) }

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ arr \in ArrayType
    /\ arr0 = arr
    /\ pending = IF N > 0 THEN {<<1, N>>} ELSE {}

-----------------------------------------------------------------------------
(* Actions *)

\* Process a single pending interval <<lo, hi>>
ProcessInterval(lo, hi) ==
    /\ <<lo, hi>> \in pending
    /\ IF lo < hi
         THEN \E p \in lo..(hi - 1) :
                /\ arr' \in PartitionResults(arr, lo, p, hi)
                /\ pending' = (pending \ {<<lo, hi>>})
                                 \cup {<<lo, p>>, <<p + 1, hi>>}
         ELSE /\ pending' = pending \ {<<lo, hi>>}
              /\ arr' = arr
    /\ UNCHANGED arr0

Step == \E iv \in pending : ProcessInterval(iv[1], iv[2])

\* Explicit terminal stuttering, so that a finished run is not reported
\* as a deadlock.
Done == /\ pending = {}
        /\ UNCHANGED vars

Next == Step \/ Done

-----------------------------------------------------------------------------
(* Fairness and specification *)

(***************************************************************************)
(* Fairness:                                                               *)
(*   - Weak fairness on Step: if some interval stays pending, a            *)
(*     processing step must eventually happen.                             *)
(*   - Weak fairness on each individual interval: an interval that stays   *)
(*     continuously pending is eventually processed, so no interval is     *)
(*     starved.                                                            *)
(*                                                                         *)
(* Termination then follows from a well-founded variant. Let the measure   *)
(* be the sum over pending intervals of (2 * length - 1). Every Step       *)
(* strictly decreases this measure, and the measure is bounded below by    *)
(* zero.                                                                   *)
(***************************************************************************)
Fairness ==
    /\ WF_vars(Step)
    /\ \A lo \in 1..N, hi \in 0..N : WF_vars(ProcessInterval(lo, hi))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Invariants *)

TypeOK ==
    /\ arr \in ArrayType
    /\ arr0 \in ArrayType
    /\ pending \subseteq Interval

\* Multiset preservation: arr is always a permutation of the original array
PermInv == IsPerm(arr, arr0)

\* Pending intervals are pairwise disjoint and lie within 1..N
DisjointInv ==
    \A iv1, iv2 \in pending :
        iv1 # iv2 =>
            (iv1[2] < iv2[1] \/ iv2[2] < iv1[1] \/ iv1[1] > iv1[2] \/ iv2[1] > iv2[2])

\* Key inductive invariant: two positions that are not inside a common
\* pending interval are already in nondecreasing order relative to each
\* other.
SortedOutsideInv ==
    \A i, j \in Idx :
        (i < j /\ ~(\E iv \in pending : InInterval(i, iv) /\ InInterval(j, iv)))
            => arr[i] <= arr[j]

\* Ordering progress: when no work remains, the array is sorted
SortedWhenDone == (pending = {}) => Sorted(arr)

Invariants ==
    /\ TypeOK
    /\ PermInv
    /\ DisjointInv
    /\ SortedOutsideInv
    /\ SortedWhenDone

-----------------------------------------------------------------------------
(* Step-level safety properties *)

\* Every step keeps the array a permutation of the previous array
StepPermutation == [][IsPerm(arr', arr)]_vars

\* Every step changes only the elements inside the interval it processes
StepPreservesOutside ==
    [][ \E iv \in pending : SameOutside(arr, arr', iv[1], iv[2]) ]_vars

\* The original array is never modified
GhostConstant == [][arr0' = arr0]_vars

-----------------------------------------------------------------------------
(* Liveness *)

\* The algorithm eventually runs out of pending intervals
Termination == <>(pending = {})

\* After termination the array remains sorted forever
EventuallySorted == <>[](pending = {} /\ Sorted(arr))

-----------------------------------------------------------------------------
(* Theorems *)

THEOREM Spec => []Invariants
THEOREM Spec => StepPermutation /\ StepPreservesOutside /\ GhostConstant
THEOREM Spec => Termination /\ EventuallySorted

=============================================================================