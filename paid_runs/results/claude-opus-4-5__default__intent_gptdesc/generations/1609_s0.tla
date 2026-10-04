-------------------------------- MODULE Quicksort --------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS 
    N,          \* Length of the array
    Values      \* Finite domain of comparable values

ASSUME N \in Nat /\ N > 0
ASSUME Values \subseteq Int /\ IsFiniteSet(Values)

VARIABLES
    arr,            \* The array being sorted (represented as a function 1..N -> Values)
    initialArr,     \* The initial array (for permutation checking)
    workStack       \* Stack of subranges (lo, hi) that still need to be sorted

vars == <<arr, initialArr, workStack>>

--------------------------------------------------------------------------------
(* Helper Definitions *)

\* The set of all indices
Indices == 1..N

\* Check if sequence s is sorted in nondecreasing order from index lo to hi
IsSortedRange(a, lo, hi) ==
    \A i, j \in lo..hi : i < j => a[i] <= a[j]

\* Check if the entire array is sorted
IsSorted(a) ==
    IsSortedRange(a, 1, N)

\* Count occurrences of value v in array a
CountVal(a, v) ==
    Cardinality({i \in Indices : a[i] = v})

\* Two arrays are permutations of each other
IsPermutation(a1, a2) ==
    \A v \in Values : CountVal(a1, v) = CountVal(a2, v)

\* A subrange is trivial (already sorted by definition) if it has 0 or 1 elements
IsTrivialRange(lo, hi) ==
    hi <= lo

\* All possible arrays of length N with values from Values
AllArrays == [Indices -> Values]

\* A range is valid
ValidRange(lo, hi) ==
    lo \in 1..N /\ hi \in 1..N /\ lo <= hi

--------------------------------------------------------------------------------
(* Partition Specification *)

\* After partitioning [lo..hi] around pivot position pivotPos:
\* - Elements outside [lo..hi] are unchanged
\* - All elements in [lo..pivotPos-1] are <= arr[pivotPos]
\* - All elements in [pivotPos+1..hi] are >= arr[pivotPos]
\* - The subarray [lo..hi] is a permutation of the original

PartitionedCorrectly(oldArr, newArr, lo, hi, pivotPos) ==
    /\ pivotPos \in lo..hi
    \* Elements outside the range are unchanged
    /\ \A i \in Indices : (i < lo \/ i > hi) => newArr[i] = oldArr[i]
    \* Left side <= pivot
    /\ \A i \in lo..(pivotPos-1) : newArr[i] <= newArr[pivotPos]
    \* Right side >= pivot
    /\ \A i \in (pivotPos+1)..hi : newArr[i] >= newArr[pivotPos]
    \* The subrange is a permutation of the original subrange
    /\ \A v \in Values : 
        Cardinality({i \in lo..hi : newArr[i] = v}) = 
        Cardinality({i \in lo..hi : oldArr[i] = v})

\* All valid partitioned arrays for a given range
ValidPartitions(oldArr, lo, hi) ==
    {<<newArr, pivotPos>> \in AllArrays \X (lo..hi) : 
        PartitionedCorrectly(oldArr, newArr, lo, hi, pivotPos)}

--------------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ arr \in AllArrays
    /\ initialArr = arr
    /\ workStack = IF N > 1 THEN {<<1, N>>} ELSE {}

--------------------------------------------------------------------------------
(* Actions *)

\* Partition a non-trivial range and push resulting subranges onto stack
Partition(lo, hi) ==
    /\ <<lo, hi>> \in workStack
    /\ ~IsTrivialRange(lo, hi)
    /\ \E newArr \in AllArrays, pivotPos \in lo..hi :
        /\ PartitionedCorrectly(arr, newArr, lo, hi, pivotPos)
        /\ arr' = newArr
        /\ workStack' = (workStack \ {<<lo, hi>>}) \cup
            (IF pivotPos > lo THEN {<<lo, pivotPos - 1>>} ELSE {}) \cup
            (IF pivotPos < hi THEN {<<pivotPos + 1, hi>>} ELSE {})
    /\ UNCHANGED initialArr

\* Remove a trivial range from the stack (single element or empty range)
RemoveTrivial ==
    /\ \E lo, hi \in 1..N : 
        /\ <<lo, hi>> \in workStack
        /\ IsTrivialRange(lo, hi)
        /\ workStack' = workStack \ {<<lo, hi>>}
    /\ UNCHANGED <<arr, initialArr>>

\* The Next-state relation
Next ==
    \/ \E lo, hi \in 1..N : 
        /\ <<lo, hi>> \in workStack
        /\ ~IsTrivialRange(lo, hi)
        /\ Partition(lo, hi)
    \/ RemoveTrivial

\* Termination - stuttering when done
Done ==
    /\ workStack = {}
    /\ UNCHANGED vars

--------------------------------------------------------------------------------
(* Fairness and Specification *)

\* Weak fairness ensures progress
Fairness ==
    /\ WF_vars(Next)

Spec == Init /\ [][Next \/ Done]_vars /\ Fairness

--------------------------------------------------------------------------------
(* Invariants *)

\* Type invariant
TypeOK ==
    /\ arr \in AllArrays
    /\ initialArr \in AllArrays
    /\ workStack \subseteq (Indices \X Indices)

\* The current array is always a permutation of the initial array
PermutationInvariant ==
    IsPermutation(arr, initialArr)

\* Elements outside any pending work range maintain their relative order established by partitioning
\* This captures that completed partitions are not disturbed
NoInterference ==
    \A <<lo1, hi1>>, <<lo2, hi2>> \in workStack :
        (<<lo1, hi1>> # <<lo2, hi2>>) => 
            (hi1 < lo2 \/ hi2 < lo1)  \* Ranges don't overlap

\* Combined safety invariant
SafetyInvariant ==
    /\ TypeOK
    /\ PermutationInvariant
    /\ NoInterference

--------------------------------------------------------------------------------
(* Safety Properties *)

\* When the algorithm terminates, the array is sorted
TerminationImpliesSorted ==
    (workStack = {}) => IsSorted(arr)

\* The array remains a permutation throughout execution
AlwaysPermutation ==
    IsPermutation(arr, initialArr)

--------------------------------------------------------------------------------
(* Liveness Properties *)

\* The algorithm eventually terminates
Termination ==
    <>(workStack = {})

\* Eventually the array is sorted
EventuallySorted ==
    <>IsSorted(arr)

\* Combined liveness: eventually sorted and permutation preserved
CorrectnessLiveness ==
    <>(IsSorted(arr) /\ IsPermutation(arr, initialArr))

--------------------------------------------------------------------------------
(* Well-foundedness for termination argument *)

\* The total number of elements in all work ranges decreases or stays same
\* and the number of non-trivial ranges decreases with each partition step
WorkMeasure ==
    Cardinality({i \in Indices : \E lo, hi \in 1..N : 
        <<lo, hi>> \in workStack /\ i \in lo..hi})

\* Number of non-trivial ranges
NonTrivialCount ==
    Cardinality({<<lo, hi>> \in workStack : ~IsTrivialRange(lo, hi)})

--------------------------------------------------------------------------------
(* Theorems to verify *)

\* Main correctness theorem: Quicksort produces a sorted permutation
THEOREM Correctness == Spec => [](TerminationImpliesSorted /\ AlwaysPermutation)

\* Termination theorem
THEOREM TerminationTheorem == Spec => Termination

================================================================================