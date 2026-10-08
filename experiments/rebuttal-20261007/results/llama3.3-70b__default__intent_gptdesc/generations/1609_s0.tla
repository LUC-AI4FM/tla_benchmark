```tla
MODULE QuicksortTLA

EXTENDS Integers, Sequences

CONSTANTS Len, Domain

VARIABLES arr, left, right, pivotIndex, sorted

Init ==
  /\ arr \in [1..Len -> Domain]
  /\ left = 1
  /\ right = Len
  /\ pivotIndex = 0
  /\ sorted = FALSE

Next ==
  IF ~sorted THEN
    /\ pivotIndex \in {left, ..., right}
    /\ arr' = [arr EXCEPT !i \in {left, ..., right} : 
                 IF i < pivotIndex THEN 
                   arr[i] <= arr[pivotIndex]
                 ELSE IF i > pivotIndex THEN 
                   arr[pivotIndex] <= arr[i]]
    /\ left' = IF left >= right THEN Len + 1 ELSE left
    /\ right' = IF left >= right THEN 0 ELSE right
    /\ sorted' = (left' > right')
    /\ pivotIndex' = 0
  ELSE
    /\ UNCHANGED <<arr, left, right, pivotIndex, sorted>>

Spec == Init /\ [][Next]_<<arr, left, right, pivotIndex, sorted>>
          /\ WF_<<arr, left, right, pivotIndex, sorted>>(Next)

THEOREM Spec => []sorted

INVARIANT PermutationInvariant ==
  LET initialArr == arr IN
  /\ Perm(initialArr, arr)
  /\ Sorted(arr)

INVARIANT PartialOrderingInvariant ==
  LET initialArr == arr IN
  /\ PartiallyOrdered(initialArr, arr)

Fairness == WF_<<arr, left, right, pivotIndex, sorted>>(Next)

THEOREM Spec => []PermutationInvariant
THEOREM Spec => []PartialOrderingInvariant

=============================================================================
```
Note: The `Perm` and `PartiallyOrdered` operators are not built-in TLA+ operators. They should be defined separately as follows:

```tla
Perm(a, b) == 
  /\ a = << >> 
  /\ b = << >>
  /\ {i \in 1..Len : a[i]} = {i \in 1..Len : b[i]}

PartiallyOrdered(a, b) == 
  /\ a = << >> 
  /\ b = << >>
  /\ \A i, j \in 1..Len : (a[i] <= a[j]) => (b[i] <= b[j])
```