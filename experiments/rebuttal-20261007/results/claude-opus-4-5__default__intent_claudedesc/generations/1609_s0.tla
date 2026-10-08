-------------------------------- MODULE QuickSort --------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N > 0

Indices == 1..N
Values == 1..N

VARIABLES arr, stack, initialArr, done

vars == <<arr, stack, initialArr, done>>

\* Check if a sequence is sorted in non-decreasing order over a range
IsSortedRange(a, lo, hi) ==
    \A i, j \in lo..hi : i < j => a[i] <= a[j]

\* Check if the entire array is sorted
IsSorted(a) ==
    IsSortedRange(a, 1, N)

\* A bag (multiset) of elements in an array over a range
BagOfRange(a, lo, hi) ==
    [v \in Values |-> Cardinality({i \in lo..hi : a[i] = v})]

\* Check if two arrays are permutations of each other
IsPermutation(a1, a2) ==
    BagOfRange(a1, 1, N) = BagOfRange(a2, 1, N)

\* Check if b is a valid partition of a over range [lo, hi]
\* with pivot at position p (in the result)
\* Elements outside [lo, hi] are unchanged
\* Elements in [lo, p-1] are <= elements in [p+1, hi]
IsValidPartition(a, b, lo, hi, p) ==
    /\ \A i \in Indices \ (lo..hi) : b[i] = a[i]
    /\ BagOfRange(a, lo, hi) = BagOfRange(b, lo, hi)
    /\ \A i \in lo..(p-1) : \A j \in (p+1)..hi : b[i] <= b[j]
    /\ \A i \in lo..(p-1) : b[i] <= b[p]
    /\ \A j \in (p+1)..hi : b[p] <= b[j]

Init ==
    /\ arr \in [Indices -> Values]
    /\ initialArr = arr
    /\ stack = IF N >= 1 THEN <<[lo |-> 1, hi |-> N]>> ELSE <<>>
    /\ done = FALSE

\* Pop a range from the stack and process it
Partition ==
    /\ ~done
    /\ stack /= <<>>
    /\ LET range == Head(stack)
           lo == range.lo
           hi == range.hi
       IN
       IF lo >= hi
       THEN \* Base case: range has 0 or 1 elements, already sorted
            /\ stack' = Tail(stack)
            /\ arr' = arr
            /\ done' = FALSE
            /\ UNCHANGED initialArr
       ELSE \* Choose pivot position and partition
            \E p \in lo..hi :
            \E newArr \in [Indices -> Values] :
                /\ IsValidPartition(arr, newArr, lo, hi, p)
                /\ arr' = newArr
                /\ LET leftRange == IF lo <= p-1 
                                    THEN <<[lo |-> lo, hi |-> p-1]>> 
                                    ELSE <<>>
                       rightRange == IF p+1 <= hi 
                                     THEN <<[lo |-> p+1, hi |-> hi]>> 
                                     ELSE <<>>
                   IN stack' = leftRange \o rightRange \o Tail(stack)
                /\ done' = FALSE
                /\ UNCHANGED initialArr

\* Terminate when stack is empty
Terminate ==
    /\ ~done
    /\ stack = <<>>
    /\ done' = TRUE
    /\ UNCHANGED <<arr, stack, initialArr>>

Next ==
    \/ Partition
    \/ Terminate

Fairness == WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

\* Type invariant
TypeOK ==
    /\ arr \in [Indices -> Values]
    /\ initialArr \in [Indices -> Values]
    /\ done \in BOOLEAN
    /\ \A i \in 1..Len(stack) : 
        /\ stack[i].lo \in 1..N
        /\ stack[i].hi \in 1..N

\* Safety: The array is always a permutation of the initial array
AlwaysPermutation ==
    IsPermutation(arr, initialArr)

\* Safety: Upon termination, the array is sorted
SortedWhenDone ==
    done => IsSorted(arr)

\* Combined safety invariant
Safety ==
    /\ AlwaysPermutation
    /\ SortedWhenDone

\* Liveness: The algorithm eventually terminates
Liveness == <>done

===============================================================================