```
MODULE Quicksort
EXTENDS Integers, Sequences

CONSTANTS ArrayLen
VARIABLES pc, stack, array

Init ==
  /\ pc = "Start"
  /\ stack = <<1, 1, ArrayLen>>
  /\ array = [i \in 1..ArrayLen |-> i]

Next ==
  /\ (pc = "Start") =>
    /\ pc' = "QS"
    /\ stack' = <<1, 1, ArrayLen>>
    /\ array' = array
  \/ (pc = "QS") =>
    /\ pc' = "ChoosePivot"
    /\ stack' = stack
    /\ array' = array
  \/ (pc = "ChoosePivot") =>
    /\ pc' = "Partition"
    /\ stack' = stack
    /\ array' = array
  \/ (pc = "Partition") =>
    (\* nondeterministically choose a pivot \*)
    /\ pc' = "QS"
    /\ stack' = <<1, 1, ArrayLen>> @@ <<(len(stack) + 1), (len(stack) + 2), ArrayLen>>
    /\ array' = [i \in 1..ArrayLen |-> IF i <= len(stack) THEN array[i] ELSE (IF array[(len(stack) + 1)] <= array[(len(stack) + 2)] THEN array[(len(stack) + 1)] ELSE array[(len(stack) + 2)])]
  \/ (pc = "QS") =>
    /\ pc' = "Done"
    /\ stack' = []
    /\ array' = array
  \/ (pc = "Done") => 
    /\ UNCHANGED <<pc, stack, array>>

Spec ==
  Init /\ [][Next]_<<pc, stack, array>>
  /\ WF_<<pc, stack, array>>(Next)

THEOREM Spec => <>[]pc = "Done"
```