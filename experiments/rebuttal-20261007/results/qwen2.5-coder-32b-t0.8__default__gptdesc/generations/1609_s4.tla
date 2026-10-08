---- MODULE QuickSortSpec ----

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS ArrayLen

VARIABLES arr, pc, stack, lo, hi, pivot, i, j

Init == /\ arr \in [1..ArrayLen -> Int]
        /\ pc = "Start"
        /\ stack = << >>
        /\ lo = 1
        /\ hi = ArrayLen
        /\ UNCHANGED <<i, j, pivot>>

QuicksortFrame(lo_, hi_) == [lo |-> lo_, hi |-> hi_]

Partition ==
    /\ i' \in {lo .. hi}
    /\ j' \in {i' .. hi}
    /\ pivot' = arr[i']
    /\ \A k \in 1..ArrayLen : 
        \/ k < lo
        \/ k > hi
        \/ (k <= i' => arr[k] = arr'[k])
        \/ (k >= j' => arr[k] = arr'[k])
    /\ \A k \in {i'+1 .. j'-1} : arr'[k] = pivot'
    /\ \A k \in {lo .. i'} : arr'[k] <= pivot'
    /\ \A k \in {j' .. hi} : arr'[k] >= pivot'

Next ==
    \/ /\ pc = "Start"
       /\ stack = << >>
       /\ lo = 1
       /\ hi = ArrayLen
       /\ pc' = "QS"
    \/ /\ pc = "QS"
       /\ lo <= hi
       /\ LET new_lo == lo
          new_hi == hi
      IN /\ stack' = Append(stack, QuicksortFrame(new_lo, new_hi))
         /\ pc' = "Partition"
    \/ /\ pc = "Partition"
       /\ Partition
       /\ IF i' < j'
          THEN /\ arr' \in [1..ArrayLen -> Int]
               /\ i'' = i' + 1
               /\ j'' = j'
               /\ pivot'' = pivot'
               /\ lo' = lo
               /\ hi' = hi
               /\ stack' = stack
               /\ pc' = "Partition"
          ELSE /\ arr' \in [1..ArrayLen -> Int]
               /\ IF i' > lo + 1
                  THEN /\ lo' = lo
                       /\ hi' = i' - 1
                  ELSE /\ lo' = lo
                       /\ hi' = lo
               /\ IF j' < hi - 1
                  THEN /\ lo'' = j' + 1
                       /\ hi'' = hi
                       /\ stack' = Append(stack, QuicksortFrame(lo'', hi''))
                  ELSE stack' = stack
               /\ pc' = "Return"
    \/ /\ pc = "Return"
       /\ stack \= << >>
       /\ LET frame == Head(stack)
          new_lo == frame[lo]
          new_hi == frame[hi]
      IN /\ lo' = new_lo
         /\ hi' = new_hi
         /\ stack' = Tail(stack)
         /\ pc' = "QS"
    \/ /\ pc = "Return"
       /\ stack = << >>
       /\ pc' = "Done"

Spec ==
    /\ Init
    /\ [][Next]_<<arr, pc, stack, lo, hi, pivot, i, j>>
    /\ WF_[Next]_<<arr, pc, stack, lo, hi, pivot, i, j>>

THEOREM Spec => []<>(pc = "Done")

Termination ==
    <>[](pc = "Done")

Sorted ==
    \A k \in 1..(ArrayLen - 1) : arr[k] <= arr[k+1]

Permutation ==
    DOMAIN arr = {1..ArrayLen}
    /\ DOMAIN arr' = {1..ArrayLen}
    /\ \E perm \in Permutations({1..ArrayLen}) :
        \A k \in DOMAIN arr : arr'[k] = arr[perm[k]]

TestState ==
    Sorted
    /\ Permutation

====