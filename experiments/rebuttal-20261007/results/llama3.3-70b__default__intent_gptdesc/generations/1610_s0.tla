```tla
MODULE Quicksort
EXTENDS Integers, Sequences

CONSTANTS N, Domain
VARIABLES array, pendingIntervals

Init ==
  /\ array \in [1..N -> Domain]
  /\ pendingIntervals = {[1, N]}

Next ==
  /\ IF pendingIntervals # {}
    THEN
      /\ \E interval \in pendingIntervals :
        /\ LET lo == interval[1]
            hi == interval[2]
         IN
           IF lo < hi
           THEN
             /\ \E p \in (lo..hi) :
               /\ \E newArray \in [1..N -> Domain] :
                 /\ newArray = [array EXCEPT !
                   [i \in (lo..p) |-> CHOOSE x \in {y \in array[lo..hi] : y <= array[p]}]
                   [i \in (p+1..hi) |-> CHOOSE x \in {y \in array[lo..hi] : y > array[p]}]]
                 /\ pendingIntervals' = (pendingIntervals \ {interval}) \cup {[lo, p], [p+1, hi]}
           ELSE
             /\ pendingIntervals' = pendingIntervals \ {interval}
      /\ array' = array
    ELSE
      /\ UNCHANGED pendingIntervals
      /\ UNCHANGED array

Spec ==
  Init /\ [][Next]_array, pendingIntervals

THEOREM Spec => []MultisetPreservation
THEOREM Spec => []ValuePreservation
THEOREM Spec => []SortedWhenDone
THEOREM Spec => <><pendingIntervals = {}>_

MultisetPreservation ==
  \A i \in 1..N : array[i] \in Domain

ValuePreservation ==
  \A interval \in pendingIntervals :
    \A i \in (1..interval[1]-1) \cup (interval[2]+1..N) :
      array[i]' = array[i]

SortedWhenDone ==
  pendingIntervals = {} =>
    \A i, j \in 1..N : i < j => array[i] <= array[j]
```