------------------------------- MODULE QuicksortSpec -------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS N \* Length of the array

VARIABLES arr, stack \* arr is the sequence representing the array, stack holds subarray indices to be sorted

Init == /\ arr \in [1..N -> DOMAIN Int]
        /\ stack = <<1, N>>

Next ==
    LET pivotIndex == CHOOSE i \in 1..N : TRUE
        pivotValue == arr[pivotIndex]
        partitionedArr == CHOOSE a \in [1..N -> DOMAIN Int] :
            /\ a = [j \in 1..N | j \notin (stack[1])..(stack[2]) -> arr[j]]
            /\ (\E k, l \in (stack[1])..(stack[2]) : k <= l => a[k] <= a[l])
            /\ (\A j \in (stack[1])..(stack[2]) : a[j] = pivotValue \/ a[j] <= pivotValue \/ a[j] >= pivotValue)
        leftSubarray == <<stack[1], CHOOSE i \in stack[1]..pivotIndex-1 : TRUE>>
        rightSubarray == <<CHOOSE i \in pivotIndex+1..stack[2] : TRUE, stack[2]>>
    IN
    \/ /\ stack # <<>>
       /\ LET currentSubarray == <<stack[1], stack[2]>>
          newStack == [IF currentSubarray[1] <= pivotIndex-1 THEN <<currentSubarray[1], pivotIndex-1>> ELSE <<>>]
                      \o [IF pivotIndex+1 <= currentSubarray[2] THEN <<pivotIndex+1, currentSubarray[2]] ELSE <<>>]
          newStack' == IF stack = <<stack[1], stack[2]>> THEN newStack ELSE stack
       IN
       /\ arr' = partitionedArr
       /\ stack' = Tail(stack) \o newStack'
    \/ /\ stack # <<>>
       /\ LET currentSubarray == Head(stack)
          newStack == [IF currentSubarray[1] <= pivotIndex-1 THEN <<currentSubarray[1], pivotIndex-1>> ELSE <<>>]
                      \o [IF pivotIndex+1 <= currentSubarray[2] THEN <<pivotIndex+1, currentSubarray[2]] ELSE <<>>]
       IN
       /\ arr' = partitionedArr
       /\ stack' = Tail(stack) \o newStack

Spec ==
    /\ Init
    /\ [][Next]_<<arr, stack>>
    /\ WF_next(<<arr, stack>>, Next)

\* Safety properties
Sorted == \A i, j \in 1..N : i <= j => arr[i] <= arr[j]
Permutation == DOMAIN arr = DOMAIN Int /\ (\A x \in DOMAIN Int : Cardinality({i \in 1..N : arr[i] = x}) = Cardinality({i \in 1..N : [Init]_<<arr, stack>> => arr'[i] = x}))

\* Liveness property
Termination == <>(stack = <<>>)

Invariant ==
    /\ Sorted
    /\ Permutation

THEOREM Spec => []Invariant /\ <>Termination
=============================================================================