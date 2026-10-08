```
MODULE Quicksort
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES pc, S, array

Init ==
  /\ pc = "Start"
  /\ S = {<<1, N>>}
  /\ array \in [1..N -> 1..N]

qs1 == 
  /\ pc = "Start"
  /\ \E interval \in S :
    /\ \E pivot \in interval :
      /\ LET left == <<i \in 1..(pivot-1) |-> i>,
            right == <<i \in (pivot+1)..N |-> i>>
        IN
          /\ array' = [array EXCEPT ![pivot] = array[pivot]]
          /\ S' = (S \ {interval}) \cup {left, right}
      /\ pc' = "Start"
  /\ \E interval \in S :
    /\ interval = <<1, 1>> 
    /\ S' = S \ {interval}
    /\ pc' = "Done"

Next ==
  /\ qs1
  /\ UNCHANGED array

Spec == Init /\ [][Next]_<<pc, S, array>>
WeakFairness == <><qs1>_<<pc, S, array>>
Termination == <>[]pc = "Done"

THEOREM Spec => []Termination
```
Note: The `UNCHANGED` operator is used to specify that the `array` variable does not change in the `Next` relation. The `WeakFairness` property specifies that the `qs1` action should be taken infinitely often, if possible. The `Termination` property asserts that the program counter eventually reaches "Done".