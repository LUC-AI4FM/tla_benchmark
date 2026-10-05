---------------------------- MODULE QuickSort ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS N, Values

ASSUME N \in Nat /\ N >= 0
ASSUME Values # {}

VARIABLES arr, pending, initialArr

vars == <<arr, pending, initialArr>>

-----------------------------------------------------------------------------
(* Helper definitions *)

\* An interval is represented as a record with lo and hi fields
Interval == [lo : 1..N, hi : 1..N]

\* Check if sequence a is a permutation of sequence b
\* by comparing element counts
CountOccurrences(seq, v) ==
    Cardinality({i \in DOMAIN seq : seq[i] = v})

IsPermutation(a, b) ==
    /\ Len(a) = Len(b)
    /\ \A v \in Values : CountOccurrences(a, v) = CountOccurrences(b, v)

\* Check if a sequence is sorted in nondecreasing order
IsSorted(seq) ==
    \A i, j \in DOMAIN seq : i < j => seq[i] <= seq[j]

\* Check if all elements in range [lo1, hi1] are <= all elements in range [lo2, hi2]
AllLessOrEqual(seq, lo1, hi1, lo2, hi2) ==
    \A i \in lo1..hi1 : \A j \in lo2..hi2 : seq[i] <= seq[j]

\* Check if two sequences agree outside a given interval
AgreeOutside(a, b, lo, hi) ==
    /\ Len(a) = Len(b)
    /\ \A i \in DOMAIN a : (i < lo \/ i > hi) => a[i] = b[i]

\* Check if seq2 is a permutation of seq1 restricted to interval [lo, hi]
IsPermutationInInterval(seq1, seq2, lo, hi) ==
    \A v \in Values :
        Cardinality({i \in lo..hi : seq1[i] = v}) = 
        Cardinality({i \in lo..hi : seq2[i] = v})

\* Set of all valid partitioned arrays given current array, interval, and pivot
ValidPartitionedArrays(currentArr, lo, hi, p) ==
    {newArr \in [1..N -> Values] :
        /\ AgreeOutside(currentArr, newArr, lo, hi)
        /\ IsPermutationInInterval(currentArr, newArr, lo, hi)
        /\ (p >= lo /\ p < hi) => AllLessOrEqual(newArr, lo, p, p+1, hi)
    }

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ arr \in [1..N -> Values]
    /\ pending = IF N >= 1 THEN {[lo |-> 1, hi |-> N]} ELSE {}
    /\ initialArr = arr

-----------------------------------------------------------------------------
(* Actions *)

\* Remove a trivial interval (lo >= hi) from pending
RemoveTrivial(interval) ==
    /\ interval \in pending
    /\ interval.lo >= interval.hi
    /\ pending' = pending \ {interval}
    /\ arr' = arr
    /\ initialArr' = initialArr

\* Partition action: pick interval, choose pivot, produce valid partitioned array
Partition(interval, p) ==
    /\ interval \in pending
    /\ interval.lo < interval.hi
    /\ p \in interval.lo..(interval.hi - 1)
    /\ \E newArr \in ValidPartitionedArrays(arr, interval.lo, interval.hi, p) :
        arr' = newArr
    /\ pending' = (pending \ {interval}) \cup 
                  {[lo |-> interval.lo, hi |-> p], [lo |-> p + 1, hi |-> interval.hi]}
    /\ initialArr' = initialArr

\* Combined next-state relation
Next ==
    \/ \E interval \in pending :
        \/ RemoveTrivial(interval)
        \/ \E p \in 1..N : Partition(interval, p)

-----------------------------------------------------------------------------
(* Fairness and Specification *)

\* Weak fairness on all enabled partition and removal actions
Fairness ==
    /\ \A interval \in Interval :
        WF_vars(RemoveTrivial(interval))
    /\ \A interval \in Interval :
        \A p \in 1..N :
            WF_vars(Partition(interval, p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety Invariants *)

\* Type invariant
TypeOK ==
    /\ arr \in [1..N -> Values]
    /\ pending \subseteq Interval
    /\ initialArr \in [1..N -> Values]

\* The array is always a permutation of the initial array
PermutationInvariant ==
    IsPermutation(arr, initialArr)

\* Safety invariant combining type correctness and permutation preservation
SafetyInvariant ==
    /\ TypeOK
    /\ PermutationInvariant

-----------------------------------------------------------------------------
(* Correctness Properties *)

\* When pending is empty, the array is sorted
Sorted == IsSorted(arr)

\* Ordering progress: termination implies sorted
OrderingProgress ==
    (pending = {}) => Sorted

\* Combined invariant
Invariant ==
    /\ SafetyInvariant
    /\ OrderingProgress

-----------------------------------------------------------------------------
(* Liveness Properties *)

\* Termination: eventually no pending intervals remain
Termination ==
    <>(pending = {})

\* The algorithm eventually produces a sorted array
EventuallySorted ==
    <>(pending = {} /\ Sorted)

=============================================================================