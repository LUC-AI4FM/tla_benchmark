```
MODULE Quicksort
EXTENDS Integers, Sequences

CONSTANTS N
VARIABLES arr, intervals

Init ==
  /\ arr \in [1..N -> 1..N]
  /\ intervals = {{1, N}}

Next ==
  /\ IF intervals = {} 
    THEN UNCHANGED <<arr, intervals>>
    ELSE
      /\ \E i \in intervals : 
        /\ IF i[2] - i[1] + 1 > 1
          THEN
            /\ \E p \in i[1]..i[2] :
              /\ \E perm \in Permutations(i[1], i[2]) :
                /\ PermHelper(arr, i[1], i[2], p, perm)
                /\ arr' = [arr EXCEPT !j \in i[1]..i[2] : arr'[j] = perm[j - i[1] + 1]]
                /\ intervals' = (intervals \ {i}) \cup {{i[1], p - 1}, {p + 1, i[2]}}
          ELSE
            /\ intervals' = intervals \ {i}
        /\ UNCHANGED arr

PermHelper(arr, l, r, p, perm) ==
  /\ perm[1] = p - l + 1
  /\ \A j \in l..p-1 : arr[j] <= arr[p]
  /\ \A j \in p+1..r : arr[p] <= arr[j]

Spec == Init /\ [][Next]_<<arr, intervals>>
THEOREM Spec => <>[]intervals = {}
```