------------------------------- MODULE QuickSortSpec -------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS N \* Length of the array

VARIABLES arr, stack \* arr is the array, stack holds subarray ranges to sort

Init == 
  /\ arr \in [0..N-1 -> INT]
  /\ stack = {[0, N-1]}

Swap(seq, i, j) ==
  seq EXCEPT ![i] = seq[j], ![j] = seq[i]

Partition(subarr, pivot) ==
  LET lt = {x \in subarr : x <= pivot}
      gt = {x \in subarr : x > pivot}
  IN CHOOSE perm \in Permutations(subarr):
       /\ Head(perm) \in lt
       /\ Tail(perm) = Append(Tail(SelectSeq(perm, lt)), SelectSeq(perm, gt))

Next ==
  \/ /\ stack /= <<>>
     /\ LET [lo, hi] = Head(stack)
        pivot = CHOOSE p \in arr[lo..hi]: TRUE
        subarr = arr[lo..hi]
        perm = Partition(subarr, pivot)
        new_arr = [arr EXCEPT ![lo..hi] = perm]
        new_stack = Tail(stack) @@ (IF lo < pivot - 1 THEN <<[lo, pivot-1]>> ELSE <<>>) @@ (IF pivot + 1 < hi THEN <<[pivot+1, hi]>> ELSE <<>>)
     IN /\ arr' = new_arr
        /\ stack' = new_stack
  \/ /\ stack = <<>>
     /\ UNCHANGED arr
     /\ UNCHANGED stack

Spec ==
  Init /\ [][Next]_<<arr, stack>>

Sorted(seq) ==
  \A i \in 0..Len(seq)-2: seq[i] <= seq[i+1]

PermutationOfOriginal ==
  \E original_arr \in [0..N-1 -> INT]:
    arr = Permute(original_arr)

Termination ==
  <>[] (stack = <<>>)

Safety ==
  Sorted(arr) /\ PermutationOfOriginal

THEOREM Spec => []Safety /\ Termination
=============================================================================