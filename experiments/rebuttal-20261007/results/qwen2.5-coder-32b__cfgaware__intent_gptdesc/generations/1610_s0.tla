---------------------------- MODULE QuickSortSpec ----------------------------

CONSTANTS N \* The number of elements in the array

VARIABLES arr, pendingIntervals \* arr is the array to be sorted, pendingIntervals is a multiset of intervals [lo, hi]

DOMAIN == 1..N \* Domain of indices for the array

\* Initial predicate: Array is initialized with N elements and pendingIntervals contains only the full interval [1, N]
Init == /\ arr \in [DOMAIN -> DOMAIN] 
        /\ pendingIntervals = {[1, N]}

\* Check if an array is sorted in nondecreasing order
Sorted(arr) == \A i \in 1..N-1 : arr[i] <= arr[i+1]

\* Check if two arrays are permutations of each other
Permutation(arr1, arr2) == Cardinality({x \in DOMAIN : arr1[x] # arr2[x]}) = 0

\* Partition operation: Given an interval [lo, hi], choose a pivot p and rearrange elements within the interval
Partition(lo, hi) ==
    CHOOSE p \in lo..hi-1 :
        LET leftPart == {arr[i] : i \in lo..p}
            rightPart == {arr[i] : i \in p+1..hi} 
        IN /\ Permutation(arr[lo..hi], leftPart \cup rightPart)
           /\ \A x \in leftPart : \A y \in rightPart : x <= y

\* Next state relation: Pick an interval, partition it if necessary, and update pending intervals
Next ==
    \/ /\ pendingIntervals = {}
    \/ CHOOSE [lo, hi] \in pendingIntervals :
        /\ lo < hi
        /\ LET p == Partition(lo, hi)
           newPending == (pendingIntervals \ {[lo, hi]}) \cup {[lo, p], [p+1, hi]}
        IN /\ arr' = [arr EXCEPT ![lo..hi] = <<Partition(lo, hi)[lo..p] >> \o <<Partition(lo, hi)[p+1..hi]>>]
           /\ pendingIntervals' = newPending
    \/ CHOOSE [lo, hi] \in pendingIntervals :
        /\ lo >= hi
        /\ arr' = arr
        /\ pendingIntervals' = (pendingIntervals \ {[lo, hi]})

\* Specification: Initial state and next-state relation
Spec == Init /\ [][Next]_<<arr, pendingIntervals>>

\* Safety property: Array remains a permutation of the original array and values outside the interval are preserved
Safety ==
    LET origArr == CHOOSE arr0 \in DOMAIN -> DOMAIN : Init
    IN \/ pendingIntervals = {}
       \/ \E [lo, hi] \in pendingIntervals :
            /\ Permutation(arr[1..lo-1], origArr[1..lo-1])
            /\ Permutation(arr[hi+1..N], origArr[hi+1..N])
            /\ Permutation(arr[lo..hi], {origArr[i] : i \in lo..hi})

\* Ordering progress: When no pending intervals remain, the array is sorted
OrderingProgress ==
    \/ pendingIntervals # {}
    \/ Sorted(arr)

\* Termination property: The algorithm eventually reaches a state with no pending intervals
Termination == <>(pendingIntervals = {}) _<<arr, pendingIntervals>>

\* Fairness assumption: Prevent starvation of enabled partition choices
WF_ST == WF_next(Next) 

=============================================================================