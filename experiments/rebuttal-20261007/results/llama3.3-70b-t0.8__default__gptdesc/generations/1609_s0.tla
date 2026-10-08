```
MODULE Quicksort
EXTENDS Integers, Sequences

CONSTANTS ArrayLen

VARIABLES pc, stack, array

Init ==
  /\ pc = "Start"
  /\ stack = << >>
  /\ array = [i \in 1..ArrayLen |-> i]

Next ==
  /\ (pc = "Start") =>
    /\ pc' = "QS"
    /\ stack' = <<1, ArrayLen>>
    /\ array' = array
  \/ (pc = "QS") =>
    /\ (LET idx == Head(stack) IN
        /\ pc' = "Partition"
        /\ stack' = Tail(stack)
        /\ array' = [array EXCEPT ![idx] = ChoosePivot(array, idx, ArrayLen)]
      )
    \/ (LET idx == Head(stack) IN
        /\ pc' = "QSRec"
        /\ stack' = <<idx + 1, ArrayLen>> @@ stack
        /\ array' = PartitionArray(array, idx, ArrayLen)
      )
  \/ (pc = "Partition") =>
    /\ pc' = "Done"
    /\ stack' = stack
    /\ array' = array
  \/ (pc = "QSRec") =>
    /\ pc' = "QS"
    /\ stack' = stack
    /\ array' = array

Spec ==
  /\ Init
  /\ [][Next]_<<pc, stack, array>>
  /\ WF_<<pc, stack, array>>(Next)

THEOREM Spec => <>[]pc = "Done"

ChoosePivot(arr, idx, len) == 
  CHOOSE x \in {arr[i] : i \in {idx..len}} : TRUE

PartitionArray(arr, idx, len) ==
  LET
    pivot == arr[idx]
    left == [i \in idx..len |-> IF arr[i] <= pivot THEN arr[i] ELSE NULL]
    right == [i \in idx..len |-> IF arr[i] > pivot THEN arr[i] ELSE NULL]
  IN
    (left ++ right)

SortInvariant ==
  /\ array' = Permute(array)
  /\ Sorted(array')

TerminationProperty ==
  []<>pc = "Done"

Sorted(arr) == 
  \A i, j \in DOMAIN arr : i < j => arr[i] <= arr[j]

Permute(arr1, arr2) == 
  \E p \in Permutations(DOMAIN arr1) : 
    \A i \in DOMAIN arr1 : arr2[p[i]] = arr1[i]
```