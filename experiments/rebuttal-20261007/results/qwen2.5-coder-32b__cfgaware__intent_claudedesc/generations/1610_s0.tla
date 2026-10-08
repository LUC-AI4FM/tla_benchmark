------------------------------- MODULE QuicksortSpec -------------------------------

CONSTANTS N \* N is a positive natural number

VARIABLES arr, intervals

\* A permutation of a set S is a bijection from S to itself
Permutation(S) == {p \in [S -> S] : DOMAIN p = S /\ ran(p) = S}

\* Partition the array around a pivot index within an interval
Partition(arr, lo, hi, pivotIdx) ==
    LET pivotVal == arr[pivotIdx]
        leftPart  == {i \in lo..pivotIdx-1 : arr[i] <= pivotVal}
        rightPart == {i \in pivotIdx+1..hi : arr[i] > pivotVal}
        middle    == {pivotIdx}
        newLeft   == DOMAIN [leftPart -> NATURAL]
        newRight  == DOMAIN [rightPart -> NATURAL]
        newMiddle == {pivotIdx}
        newLo     == lo + CARDINALITY(newLeft)
        newHi     == hi - CARDINALITY(newRight)
    IN
        CHOOSE perm \in Permutation(leftPart \cup rightPart):
            /\ arr' = [arr EXCEPT ![lo..newLo-1] = <<perm[i] : i \in leftPart>>,
                             ![pivotIdx] = pivotVal,
                             ![newLo+1..newHi] = <<perm[i] : i \in rightPart>>]
            /\ newLeft = {i \in lo..newLo-1}
            /\ newRight = {i \in newLo+1..newHi}

\* Initial predicate: array is a permutation of 1..N and intervals contains the full array interval
Init == /\ arr \in Permutation(1..N)
        /\ intervals = {(1, N)}

\* Next state action: choose an interval to partition
Next ==
    \/ /\ intervals = {}
       /\ UNCHANGED <<arr, intervals>>
    \/ /\ CHOOSE (lo, hi) \in intervals:
           /\ lo <= hi
           /\ \/ /\ lo = hi
                  /\ intervals' = intervals \ {(lo, hi)}
              \/ /\ lo < hi
                 /\ CHOOSE pivotIdx \in lo..hi:
                    /\ LET arr'' == [arr EXCEPT ![pivotIdx] = arr[pivotIdx]]
                       IN
                          /\ Partition(arr'', lo, hi, pivotIdx)
                          /\ intervals' = (intervals \ {(lo, hi)}) \cup
                                           (IF newLo - lo > 0 THEN {(lo, newLo-1)} ELSE {})
                                           \cup
                                           (IF hi - newHi > 0 THEN {(newHi+1, hi)} ELSE {})

\* Specification: initial state and next-state relation
Spec == Init /\ [][Next]_<<arr, intervals>>

\* Termination: no more intervals to partition
Termination == intervals = {}

=============================================================================