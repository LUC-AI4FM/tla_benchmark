------------------------------- MODULE MergeSortSpec -------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS N \* Length of the array

VARIABLES array, tempArray, left, right, mid, done

Init == /\ array \in [1..N -> Int]
        /\ tempArray = << >>
        /\ left = 1
        /\ right = N
        /\ mid = (left + right) \div 2
        /\ done = FALSE

Sorted(subarray) ==
    \A i, j \in DOMAIN subarray : i < j => subarray[i] <= subarray[j]

Permutation(oldArray, newArray) ==
    Multiset(oldArray) = Multiset(newArray)

Merge ==
    /\ mid \in [left..right]
    /\ tempArray' = array[left .. right]
    /\ \E k \in 1..(right - left + 1):
        LET i == left
            j == mid + 1
            m == left - 1
        IN /\ array' = [array EXCEPT ![m+k] = IF i > mid THEN tempArray[j]
                                                   ELSE IF j > right THEN tempArray[i]
                                                   ELSE IF tempArray[i] <= tempArray[j] THEN tempArray[i]
                                                   ELSE tempArray[j]]
           /\ (i > mid \/ j > right)

Split ==
    /\ left < right
    /\ mid = (left + right) \div 2
    /\ UNCHANGED <<array, tempArray>>
    /\ left' = left
    /\ right' = mid

MergeStep ==
    /\ left < right
    /\ mid = (left + right) \div 2
    /\ Merge
    /\ left' = left
    /\ right' = right

Complete ==
    /\ done' = TRUE
    /\ UNCHANGED <<array, tempArray, left, right>>

Next == \/ Split
        \/ MergeStep
        \/ /\ left = 1
           /\ right = N
           /\ Complete

Spec == Init /\ [][Next]_<<array, tempArray, left, right, done>> /\ <><Complete>_<<array, tempArray, left, right, done>>

Sortedness == Sorted(array)

Termination == <>[](done => UNCHANGED array)

TypeOK ==
    /\ array \in [1..N -> Int]
    /\ tempArray \in SUBSEQ(Int)
    /\ left \in 1..N
    /\ right \in 1..N
    /\ mid \in 1..N
    /\ done \in BOOLEAN

Invariants == Sortedness /\ Permutation(array, array) /\ TypeOK

THEOREM Spec => []Invariants

Liveness == Termination

=============================================================================