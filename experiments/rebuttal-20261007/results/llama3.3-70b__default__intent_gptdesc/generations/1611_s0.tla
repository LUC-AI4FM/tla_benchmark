```tla
MODULE Mergesort

EXTENDS Integers, Sequences

CONSTANTS Len
VARIABLES array, temp, left, right, mid, done

Init ==
  /\ array \in [1..Len -> Int]
  /\ temp = <<>>
  /\ left = 1
  /\ right = Len
  /\ mid = 0
  /\ done = FALSE

Sort(left, right) ==
  IF left < right THEN
    /\ mid = (left + right) \div 2
    /\ Sort(left, mid)
    /\ Sort(mid + 1, right)
    /\ Merge(left, mid, right)
  ELSE TRUE

Merge(left, mid, right) ==
  /\ temp = <<>>
  /\ WHILE Len(temp) < (right - left + 1) DO
      IF Len(temp) = 0 OR array[left] <= array[mid + 1] THEN
        /\ temp := Append(temp, array[left])
        /\ left := left + 1
      ELSE
        /\ temp := Append(temp, array[mid + 1])
        /\ mid := mid + 1
      END
  /\ array := [i \in 1..Len |-> IF i >= left AND i <= right THEN temp[i - left] ELSE array[i]]
  /\ left = right + 1

Next ==
  IF ~done THEN
    /\ Sort(1, Len)
    /\ done := TRUE
  ELSE
    /\ UNCHANGED <<array, temp, left, right, mid, done>>

Spec == Init /\ [][Next]_<<array, temp, left, right, mid, done>>
          /\ WF_Vars(<<Sort>>)

THEOREM Spec => []<>(done /\ Sorted(array))
THEOREM Spec => []<>(done /\ Perm(array, array'))

Sorted(array) ==
  \A i, j \in 1..Len : i < j => array[i] <= array[j]

Perm(array1, array2) ==
  \A x \in Int : Cardinal({i \in 1..Len : array1[i] = x}) =
                    Cardinal({i \in 1..Len : array2[i] = x})

WF_Vars(<<Sort>>) == <><<Sort>>_array

=============================================================================
```
Note: The `THEOREM` statements are not part of the TLA+ specification itself, but rather a way to express the desired properties that should be proven about the specification. In practice, you would use a model checker or proof assistant like TLC or Isabelle to verify these properties.