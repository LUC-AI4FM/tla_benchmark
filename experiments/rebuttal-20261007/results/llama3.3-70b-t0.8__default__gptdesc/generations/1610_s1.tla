```
MODULE Quicksort
EXTENDS Integers, Sequences

CONSTANTS N
VARIABLES pc, array, setOfSubarrays

Init ==
  /\ pc = "Start"
  /\ array = [i \in 1..N |-> i]
  /\ setOfSubarrays = {[1, N]}

qs1 ==
  /\ pc = "Start"
  /\ \E interval \in setOfSubarrays :
    /\ \E pivot \in interval :
      /\ Let left == << << <<
            /\ array' = [i \in 1..N |-> IF i < pivot THEN Min([array[j] \in {j \in 1..N : j < pivot}]) ELSE IF i > pivot THEN Max([array[j] \in {j \in 1..N : j > pivot}]) ELSE array[i]]
            /\ setOfSubarrays' = (setOfSubarrays \ {interval}) \cup {[interval[1], pivot - 1], [pivot + 1, interval[2]]}
          >>>
        /\ pc' = "Start"
      /\ UNCHANGED pc

Next ==
  qs1
  \/ (pc = "Done" /\ UNCHANGED <<pc, array, setOfSubarrays>>)

Spec ==
  /\ Init
  /\ [][Next]_<<pc, array, setOfSubarrays>>
  /\ WF_<<pc, array, setOfSubarrays>>(Next)
  /\ []<>(pc = "Done")

THEOREM Spec => []<>(pc = "Done")
```