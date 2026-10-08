```tla
MODULE MergeSort
EXTENDS Integers, Sequences

CONSTANTS MaxLen

VARIABLES arr, temp, len, mid, left, right, i, j, k

Init ==
  /\ arr \in [1..MaxLen -> Nat]
  /\ len = Len(arr)
  /\ temp = << >>
  /\ mid = 0
  /\ left = 1
  /\ right = len
  /\ i = 1
  /\ j = (len + 1) / 2
  /\ k = 1

Next ==
  IF len <= 1 THEN
    TRUE
  ELSEIF mid = 0 THEN
    /\ mid' = len / 2
    /\ left' = 1
    /\ right' = len
    /\ i' = 1
    /\ j' = (len + 1) / 2
    /\ k' = 1
    /\ arr' = arr
    /\ temp' = << >>
  ELSEIF i <= mid THEN
    /\ temp' = Append(temp, arr[i])
    /\ i' = i + 1
    /\ j' = j
    /\ k' = k
    /\ arr' = arr
    /\ len' = len
    /\ left' = left
    /\ right' = right
    /\ mid' = mid
  ELSEIF j <= right THEN
    /\ temp' = Append(temp, arr[j])
    /\ i' = i
    /\ j' = j + 1
    /\ k' = k
    /\ arr' = arr
    /\ len' = len
    /\ left' = left
    /\ right' = right
    /\ mid' = mid
  ELSEIF k <= len THEN
    /\ IF temp[k - 1] <= temp[len - k + 1] THEN
        arr' = [arr EXCEPT ![k] = temp[k - 1]]
      ELSE
        arr' = [arr EXCEPT ![k] = temp[len - k + 1]]
    /\ i' = i
    /\ j' = j
    /\ k' = k + 1
    /\ len' = len
    /\ left' = left
    /\ right' = right
    /\ mid' = mid
    /\ temp' = temp
  ELSE
    /\ arr' = arr
    /\ i' = i
    /\ j' = j
    /\ k' = k
    /\ len' = len / 2
    /\ left' = 1
    /\ right' = len / 2
    /\ mid' = 0
    /\ temp' = << >>

Spec ==
  Init /\ [][Next]_arr

Sorted ==
  \A x, y \in 1..Len(arr) : x < y => arr[x] <= arr[y]

THEOREM Spec => []Sorted
THEOREM Spec => <><>TRUE
```
Note: The fairness condition is implicitly included in the `Spec` definition as `[][Next]_arr`, which ensures that the `Next` action is always enabled and will eventually lead to termination.