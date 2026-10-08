```
MODULE Quicksort
EXTENDS Integers, Sequences

CONSTANTS Len

VARIABLES arr, pc, done

Init ==
  /\ arr \in [1..Len -> Nat]
  /\ pc = 1
  /\ done = FALSE

Next ==
  IF ~done THEN
    /\ pc <= Len
    /\ E pivot \in {pc..Len} :
      /\ arr' = [arr EXCEPT !i \in {pc..Len} : 
                  IF i < pivot THEN arr[i] <= arr[pivot]
                  ELSE IF i > pivot THEN arr[pivot] <= arr[i]]
      /\ pc' = IF Len = pc + 1 THEN Len + 1 ELSE pc + 1
      /\ done' = (pc' = Len + 1)
    /\ UNCHANGED done
  ELSE
    /\ UNCHANGED arr
    /\ UNCHANGED pc
    /\ UNCHANGED done

Spec == Init /\ [][Next]_arr

Sorted(arr) ==
  \A i, j \in 1..Len : i < j => arr[i] <= arr[j]

Permutation(arr0, arr1) ==
  \A x \in Nat : (x \in Range(arr0)) <=> (x \in Range(arr1))

TypeInvariant == 
  /\ arr \in [1..Len -> Nat]
  /\ pc \in Nat
  /\ done \in BOOLEAN

SafetyInv == 
  /\ TypeInvariant
  /\ Permutation([arr]_e, arr)

Liveness == <>done

THEOREM Spec => []Sorted(arr)
THEOREM Spec => []Permutation([arr]_e, arr)
THEOREM Spec => Liveness
```
Note: The `[arr]_e` notation refers to the initial value of `arr`, which is captured by the `_e` (for "initial") subscript. This allows us to compare the final permutation with the original array in the safety property.