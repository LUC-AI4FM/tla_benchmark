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
    /\ pc' = "Process"
    /\ S' = S \ {interval}
    /\ \E pivot \in interval : 
      /\ arr' = [arr EXCEPT !i \in 1..N : 
        IF i < pivot THEN 
          arr'[i] \in {x \in 1..N : x <= arr[pivot]}
        ELSE IF i > pivot THEN 
          arr'[i] \in {x \in 1..N : x >= arr[pivot]}
        ELSE 
          arr'[i] = arr[pivot]]
    /\ UNCHANGED S

Next == 
  /\ pc = "Start" => qs1
  /\ pc = "Process" => 
    /\ IF S # {} THEN 
      /\ \E interval \in S : 
        /\ pc' = "Process"
        /\ S' = S \ {interval}
        /\ \E pivot \in interval : 
          /\ arr' = [arr EXCEPT !i \in 1..N : 
            IF i < pivot THEN 
              arr'[i] \in {x \in 1..N : x <= arr[pivot]}
            ELSE IF i > pivot THEN 
              arr'[i] \in {x \in 1..N : x >= arr[pivot]}
            ELSE 
              arr'[i] = arr[pivot]]
        /\ UNCHANGED S
      /\ pc' = "Done"
    /\ pc' = "Done" => UNCHANGED <<pc, S, arr>>
  /\ pc' = "Done" => S = {}

Spec == Init /\ [][Next]_<<pc, S, arr>>
Termination == <>(pc = "Done")
Fairness == WF_(Next)(<<"Start">>)
THEOREM Spec => []S \subseteq {<<a, b>> \in Nat \X Nat : a <= b}
THEOREM Spec => []Termination
```
Note that in TLA+, `\X` represents the set of all functions from one set to another. `UNCHANGED` is used to represent the fact that some variables remain unchanged during a step. The `WF_` operator is used for weak fairness, and `<><p>` is true if `p` is true at some point in time (i.e., it represents eventual truth).