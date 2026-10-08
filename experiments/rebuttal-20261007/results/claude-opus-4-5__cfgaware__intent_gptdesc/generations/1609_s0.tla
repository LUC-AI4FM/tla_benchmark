---------------------------- MODULE Quicksort ----------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT ArrayLen

ASSUME ArrayLen \in Nat /\ ArrayLen > 0

VARIABLES array, stack, initialArray, done

vars == <<array, stack, initialArray, done>>

\* Domain of values in the array
Values == 1..ArrayLen

\* A range represents a subarray [lo, hi] to be sorted
Range == [lo: 1..ArrayLen, hi: 1..ArrayLen]

\* Check if a sequence is a permutation of another
IsPermutation(s1, s2) ==
    /\ Len(s1) = Len(s2)
    /\ \A v \in Values : 
        Cardinality({i \in 1..Len(s1) : s1[i] = v}) = 
        Cardinality({i \in 1..Len(s2) : s2[i] = v})

\* Check if a sequence is sorted in nondecreasing order
IsSorted(s) ==
    \A i, j \in 1..Len(s) : i < j => s[i] <= s[j]

\* Check if a subarray [lo, hi] is sorted
SubarraySorted(s, lo, hi) ==
    \A i, j \in lo..hi : i < j => s[i] <= s[j]

\* All permutations of a set of values
PermutationsOf(vals) ==
    LET n == Cardinality(vals)
        seqs == [1..n -> vals]
    IN {s \in seqs : \A v \in vals : Cardinality({i \in 1..n : s[i] = v}) = 1}

\* Initial state: array contains some permutation of 1..ArrayLen
Init ==
    /\ array \in PermutationsOf(Values)
    /\ initialArray = array
    /\ stack = IF ArrayLen > 1 THEN {[lo |-> 1, hi |-> ArrayLen]} ELSE {}
    /\ done = FALSE

\* Partition step: atomically partition a subarray around a pivot
\* This models the partition operation abstractly
Partition ==
    /\ ~done
    /\ stack /= {}
    /\ \E range \in stack :
        /\ range.lo < range.hi  \* Non-trivial range
        /\ \E pivotIdx \in range.lo..range.hi :  \* Choose pivot position
            \E finalPivotPos \in range.lo..range.hi :  \* Final position of pivot
                \E newArray \in [1..ArrayLen -> Values] :
                    \* Elements outside [lo, hi] unchanged
                    /\ \A i \in 1..ArrayLen : 
                        (i < range.lo \/ i > range.hi) => newArray[i] = array[i]
                    \* Subarray [lo, hi] is a permutation of original subarray
                    /\ \A v \in Values :
                        Cardinality({i \in range.lo..range.hi : newArray[i] = v}) =
                        Cardinality({i \in range.lo..range.hi : array[i] = v})
                    \* All elements left of pivot <= all elements right of pivot
                    /\ \A i \in range.lo..(finalPivotPos-1) :
                        \A j \in (finalPivotPos+1)..range.hi :
                            newArray[i] <= newArray[j]
                    \* Elements left of pivot <= pivot element
                    /\ \A i \in range.lo..(finalPivotPos-1) :
                        newArray[i] <= newArray[finalPivotPos]
                    \* Elements right of pivot >= pivot element
                    /\ \A j \in (finalPivotPos+1)..range.hi :
                        newArray[finalPivotPos] <= newArray[j]
                    \* Update state
                    /\ array' = newArray
                    /\ stack' = (stack \ {range}) \cup
                        (IF finalPivotPos - 1 > range.lo 
                         THEN {[lo |-> range.lo, hi |-> finalPivotPos - 1]}
                         ELSE {}) \cup
                        (IF finalPivotPos + 1 < range.hi
                         THEN {[lo |-> finalPivotPos + 1, hi |-> range.hi]}
                         ELSE {})
                    /\ initialArray' = initialArray
                    /\ done' = FALSE

\* Handle trivial ranges (single element or invalid range)
SkipTrivial ==
    /\ ~done
    /\ stack /= {}
    /\ \E range \in stack :
        /\ range.lo >= range.hi
        /\ stack' = stack \ {range}
        /\ array' = array
        /\ initialArray' = initialArray
        /\ done' = FALSE

\* Mark as done when stack is empty
Finish ==
    /\ ~done
    /\ stack = {}
    /\ done' = TRUE
    /\ array' = array
    /\ stack' = stack
    /\ initialArray' = initialArray

\* Stuttering step (for completeness)
Stutter ==
    /\ done
    /\ UNCHANGED vars

Next == Partition \/ SkipTrivial \/ Finish \/ Stutter

\* Fairness: require progress when work remains
Fairness == WF_vars(Partition \/ SkipTrivial \/ Finish)

Spec == Init /\ [][Next]_vars /\ Fairness

\* ====================