---------------------------- MODULE Quicksort ----------------------------
EXTENDS Integers, Sequences

CONSTANT N

VARIABLE arr, intervals

Permutation(seq) == { [i \in 1..Len(seq)] |-> seq[i] : i \in 1..Len(seq) }

Partition(arr, left, right, pivot) ==
  LET partitioned == [i \in left..right |-> IF i = pivot THEN arr[pivot]
                                             ELSE IF arr[i] <= arr[pivot]
                                             THEN CHOOSE j \in left..pivot-1 : TRUE
                                             ELSE CHOOSE j \in pivot+1..right : TRUE ]
  IN  [i \in 1..N |-> IF i \in left..right THEN partitioned[i]
                     ELSE arr[i] ]

Next(arr, intervals) ==
  /\ intervals # {}
  /\ CHOOSE <<left, right>> \in intervals : TRUE
  /\ IF right - left > 0
     THEN
       /\ CHOOSE pivot \in left..right : TRUE
       /\ arr' = Partition(arr, left, right, pivot)
       /\ intervals' = (intervals \ {<<left, right>>}) \cup {<<left, pivot-1>>, <<pivot+1, right>>}
     ELSE
       /\ arr' = arr
       /\ intervals' = intervals \ {<<left, right>>}

Spec == 
  /\ arr \in [1..N -> 1..N]
  /\ intervals = {<<1, N>>}
  /\ [][Next(arr, intervals)]

Termination == <>[](~intervals # {})

THEOREM Spec => []Termination
=============================================================================