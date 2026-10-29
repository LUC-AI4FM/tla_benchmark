------------------------------ MODULE QuickSort ------------------------------
(***************************************************************************)
(* Abstract, high-level model of Quicksort over a fixed-length array.     *)
(*                                                                         *)
(* The array is a function 1..N -> Values. The recursion is modelled by a *)
(* set U of pending (unsorted) subranges <<lo, hi>>. A partition step is  *)
(* atomic. It picks any pending subrange and any pivot index in it. It    *)
(* then produces any rearrangement of that subrange that meets three      *)
(* conditions: it is a permutation of the subrange, the pivot value lands *)
(* at a chosen position p, and every element left of p is <= the pivot    *)
(* value, which is <= every element right of p.                           *)
(* The step leaves every element outside the subrange unchanged. The      *)
(* subranges lo..p-1 and p+1..hi then replace the processed subrange, but *)
(* only when they hold at least 2 elements.                               *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    N,        \* length of the array
    Values    \* finite domain of comparable (integer) values

ASSUME NAssump      == N \in Nat
ASSUME ValuesAssump == /\ Values \subseteq Int
                       /\ IsFiniteSet(Values)
                       /\ Values # {}

VARIABLES
    arr,      \* the array being sorted
    init,     \* ghost copy of the initial array (for the permutation property)
    U         \* set of pending subranges <<lo, hi>> still to be sorted

vars == <<arr, init, U>>

Idx    == 1..N
Ranges == { r \in Idx \X Idx : r[1] < r[2] }   \* subranges with >= 2 elements

Rng(r) == r[1]..r[2]

-----------------------------------------------------------------------------
(* Helper operators *)

\* Number of occurrences of value v in array a
Count(a, v) == Cardinality({ i \in Idx : a[i] = v })

\* a and b hold the same multiset of values
IsPerm(a, b) == \A v \in Values : Count(a, v) = Count(b, v)

Sorted(a) == \A i, j \in Idx : i < j => a[i] <= a[j]

\* Positions i and j lie in the same pending subrange
SameRange(i, j) == \E r \in U : i \in Rng(r) /\ j \in Rng(r)

\* Position i lies in no pending subrange
Untouchable(i) == \A r \in U : i \notin Rng(r)

\* Termination measure: total length of pending subranges
RECURSIVE SumLen(_)
SumLen(S) == IF S = {} THEN 0
             ELSE LET r == CHOOSE x \in S : TRUE
                  IN  (r[2] - r[1] + 1) + SumLen(S \ {r})

Measure == SumLen(U)

\* Sub-ranges of length >= 2 produced by splitting at p
SubRanges(lo, p, hi) ==
    (IF lo < p - 1 THEN { <<lo, p - 1>> } ELSE {})
    \cup
    (IF p + 1 < hi THEN { <<p + 1, hi>> } ELSE {})

-----------------------------------------------------------------------------
(* Initial state: an arbitrary array of values; the whole array is pending *)

Init ==
    /\ arr \in [Idx -> Values]
    /\ init = arr
    /\ U = IF N > 1 THEN { <<1, N>> } ELSE {}

-----------------------------------------------------------------------------
(* Atomic partition step on pending subrange r *)

Partition(r) ==
    LET lo == r[1]
        hi == r[2]
    IN
    \E pv \in lo..hi, p \in lo..hi, B \in [Idx -> Values] :
        \* (1) no interference outside the current subarray
        /\ \A i \in Idx \ (lo..hi) : B[i] = arr[i]
        \* rearrangement only: no elements lost or created
        /\ IsPerm(B, arr)
        \* (2) the chosen pivot element ends at position p
        /\ B[p] = arr[pv]
        \* (3) left part <= pivot <= right part
        /\ \A i \in lo..(p - 1) : B[i] <= B[p]
        /\ \A j \in (p + 1)..hi : B[p] <= B[j]
        /\ arr' = B
        \* recursion: replace r by its left and right subproblems
        /\ U' = (U \ {r}) \cup SubRanges(lo, p, hi)
        /\ UNCHANGED init

PartitionStep == \E r \in U : Partition(r)

Done == U = {}

\* Stuttering once sorting is finished (avoids deadlock)
Terminated == Done /\ UNCHANGED vars

Next == PartitionStep \/ Terminated

\* Weak fairness on Next. With it, progress continues while U # {}.
\* The well-founded measure ensures termination.
Spec == Init /\ [][Next]_vars /\ WF_vars(PartitionStep)

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK ==
    /\ arr  \in [Idx -> Values]
    /\ init \in [Idx -> Values]
    /\ U \subseteq Ranges

\* Pending subranges are pairwise disjoint
DisjointRanges ==
    \A r1, r2 \in U : r1 # r2 => Rng(r1) \cap Rng(r2) = {}

\* Permutation preservation: no elements lost or created
PermutationInv == IsPerm(arr, init)

\* Partial order from completed partitions: two positions that are not in
\* the same pending subrange are already in nondecreasing order
PartialOrderInv ==
    \A i, j \in Idx : (i < j /\ ~SameRange(i, j)) => arr[i] <= arr[j]

\* Final correctness: when done, the array is sorted and is a permutation
\* of the initial array
Correctness == Done => (Sorted(arr) /\ IsPerm(arr, init))

\* The termination measure is a natural number
MeasureInv == Measure \in Nat /\ Measure <= N

Inv ==
    /\ TypeOK
    /\ DisjointRanges
    /\ PermutationInv
    /\ PartialOrderInv
    /\ Correctness
    /\ MeasureInv

-----------------------------------------------------------------------------
(* Action properties *)

\* No interference: a position outside every pending subrange never changes
NoInterference ==
    [][\A i \in Idx : Untouchable(i) => arr'[i] = arr[i]]_vars

\* The initial snapshot is never modified
InitConstant == [][init' = init]_vars

\* Well-foundedness: every partition step strictly decreases the measure
MeasureDecreases == [][PartitionStep => Measure' < Measure]_vars

\* Once done, the system stays done and the array never changes again
StableWhenDone == [][Done => (Done' /\ arr' = arr)]_vars

-----------------------------------------------------------------------------
(* Liveness *)

\* Quicksort terminates
Termination == <>Done

\* Eventually the array is permanently sorted
EventuallySorted == <>[](Sorted(arr) /\ IsPerm(arr, init))

-----------------------------------------------------------------------------
THEOREM Spec => []Inv
THEOREM Spec => NoInterference /\ InitConstant /\ MeasureDecreases /\ StableWhenDone
THEOREM Spec => Termination /\ EventuallySorted
=============================================================================