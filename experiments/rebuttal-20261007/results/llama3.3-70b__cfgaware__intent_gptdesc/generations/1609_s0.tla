---------------------------- MODULE Quicksort ----------------------------
EXTENDS Integers, Sequences

CONSTANT ArrayLen
VARIABLE arr, left, right

Spec == 
  /\ arr \in [1..ArrayLen -> Int]
  /\ left = 1
  /\ right = ArrayLen
  /\ WF_Vars(Step)
  /\ [](Termination => <>[]Termination)

Step == 
  /\ left <= right
  /\ IF left < right THEN 
    /\ \E pivot \in left..right : 
      /\ Partition(arr, left, right, pivot)
      /\ arr' = Rearrange(arr, left, right, pivot)
      /\ left' = left
      /\ right' = right
    ELSE 
      /\ UNCHANGED <<arr, left, right>>
  ELSE 
    /\ UNCHANGED <<arr, left, right>>

Partition(arr, left, right, pivot) == 
  /\ \E idx \in left..right : 
    /\ arr[pivot] = arr'[idx]
    /\ \A i \in left..(idx-1) : arr'[i] <= arr'[idx]
    /\ \A i \in (idx+1)..right : arr'[idx] <= arr'[i]

Rearrange(arr, left, right, pivot) == 
  /\ \E idx \in left..right : 
    /\ arr[pivot] = arr'[idx]
    /\ \A i \in left..(idx-1) : arr'[i] <= arr'[idx]
    /\ \A i \in (idx+1)..right : arr'[idx] <= arr'[i]

Termination == 
  /\ left >= right
  /\ IsSorted(arr, left, right)

IsSorted(arr, left, right) == 
  /\ \A i \in left..(right-1) : arr[i] <= arr[i+1]

WF_Vars(Step) == 
  /\ []<<left, right>> : Step

THEOREM Spec => []Termination
=============================================================================