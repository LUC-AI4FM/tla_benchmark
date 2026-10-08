```
MODULE Quicksort
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES pc, S, arr

Init ==
  /\ pc = "Start"
  /\ S = {<<1, N>>}
  /\ arr \in [1..N -> 1..N]

qs1 ==
  /\ pc = "Start"
  /\ \E interval \in S :
    /\ \E pivot \in interval :
      /\ Let
            left == <<i \in 1..(pivot-1) : TRUE>>
            ; mid == <<i \in {pivot} : TRUE>>
            ; right == <<i \in (pivot+1)..N : TRUE>>
          In
            /\ arr' \in [1..N -> 1..N]
            /\ \A i \in left : arr'[i] < arr[pivot]
            /\ \A i \in mid : arr'[i] = arr[pivot]
            /\ \A i \in right : arr'[i] > arr[pivot]
            /\ S' = (S \ {interval}) \cup {<<1, pivot-1>>, <<pivot+1, N>>}
            /\ pc' = "Start"
      /\ UNCHANGED pc

Next ==
  qs1
  \/ (pc = "Start" /\ S = {} /\ pc' = "Done" /\ UNCHANGED S /\ UNCHANGED arr)

Spec == Init /\ [][Next]_<<pc, S, arr>>
Termination == <>(pc = "Done")

THEOREM Spec => []Termination
```
Note: The `UNCHANGED` keyword is used to specify that certain variables do not change in a given step. The `[]` operator denotes the always operator (i.e., a property must hold at all steps), and the `<>` operator denotes the eventually operator (i.e., a property must hold at some step).