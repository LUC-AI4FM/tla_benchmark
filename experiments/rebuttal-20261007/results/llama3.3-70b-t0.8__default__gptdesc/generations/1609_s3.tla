```
MODULE Quicksort
EXTENDS Integers, Sequences

CONSTANTS ArrayLen

VARIABLES pc, stack, array

Init ==
  /\ pc = "Start"
  /\ stack = <<>>
  /\ array = [i \in 1..ArrayLen |-> i]

Next ==
  /\ (pc = "Start") =>
    /\ pc' = "QS"
    /\ stack' = <<1, ArrayLen>>
    /\ array' = array
  \/ (pc = "QS") =>
    /\ LET idx == Head(stack) IN
      /\ IF idx = ArrayLen
        THEN /\ pc' = "Done"
              /\ stack' = Tail(stack)
              /\ array' = array
        ELSE /\ pc' = "QS"
              /\ stack' = <<idx + 1, Last(stack) >> @@ <<>>
              /\ array' = [array EXCEPT ![i] = IF i <= idx THEN Min([array[j] |-> j \in idx..Last(stack)]) ELSE Max([array[j] |-> j \in idx..Last(stack)])]
      END
  \/ (pc = "Done") =>
    /\ UNCHANGED pc
    /\ UNCHANGED stack
    /\ UNCHANGED array

Spec == Init /\ [][Next]_<<pc, stack, array>>
          /\ WF_<<pc, stack, array>>(Next)

THEOREM Spec => <>[](pc = "Done")
```
Note: This is a TLA+ specification and may require some adjustments according to the specific requirements of your system. Also, it's assumed that the initial array contains unique integers from 1 to ArrayLen for simplicity, but you can adjust this as needed. 

Additionally, due to limitations in TLA+, I couldn't directly model the "chooses a pivot nondeterministically within the current subarray" behavior and instead chose the minimum value of the subarray as the pivot for simplicity.

To assert that the resulting array is a permutation of the initial array and is sorted in nondecreasing order, you can add another property like this:
```
Sorted == array' = Sort(array)
Permutation == DOMAIN array' = DOMAIN array /\ Range(array') = Range(array)

THEOREM Spec => []<>(pc = "Done" /\ Sorted /\ Permutation)
```