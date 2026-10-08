---------------------------- MODULE QuickSort ----------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS ArrayLen

VARIABLES pc, stack, arr, pivot, i, j, temp, initArr

Init == 
  /\ pc = "Start"
  /\ stack = << >>
  /\ i = 0
  /\ j = ArrayLen - 1
  /\ arr \in [0 .. ArrayLen-1 -> Nat]
  /\ initArr = arr
  /\ UNCHANGED <<pivot, temp>>

Next ==
  \/ /\ pc = "Start"
     /\ stack = << >>
     /\ i = 0
     /\ j = ArrayLen - 1
     /\ pc' = "QS"

  \/ /\ pc = "QS"
     /\ LET lo == IF stack = << >> THEN i ELSE FST(LAST(stack))
          hi == IF stack = << >> THEN j ELSE SND(LAST(stack)) IN
        <lo <= hi> 
        /\ pivot \in {arr[k] : k \in lo .. hi}
        /\ EXISTS perm \in Permutations({arr[k] : k \in lo .. hi}) :
            \/ /\ i' = lo
               /\ j' = hi
               /\ arr' = [arr EXCEPT ![k] = perm[k-lo] : k \in lo .. hi]
               /\ pc' = "Partition"
          \/ /\ i' = lo
             /\ j' = hi
             /\ arr' = arr
             /\ stack' = Append(stack, <<lo, hi>>)
             /\ i' = lo
             /\ j' = pivot - 1
             /\ pc' = "QS"

  \/ /\ pc = "Partition"
     /\ LET lo == IF stack = << >> THEN i ELSE FST(LAST(stack))
          hi == IF stack = << >> THEN j ELSE SND(LAST(stack)) IN
        <lo <= hi> 
        /\ /\ WHILE i' <= j' DO
                \E k \in i' .. j' : arr[k] > pivot
                /\ i'' = CHOOSE k \in i' .. j' : arr[k] > pivot
                /\ /\ IF i'' <= j' THEN
                        \A m \in i' .. i''-1 : arr[m] <= pivot
                    ELSE
                        TRUE
                /\ WHILE j' >= i'' DO
                        \E k \in i'' .. j' : arr[k] <= pivot
                        /\ j'' = CHOOSE k \in i'' .. j' : arr[k] <= pivot
                        /\ /\ IF j'' >= i'' THEN
                                \A m \in j''+1 .. j' : arr[m] > pivot
                            ELSE
                                TRUE
                /\ IF i'' < j'' THEN
                       temp' = arr[i']
                       /\ arr' = [arr EXCEPT ![i'] = arr[j'], ![j''] = temp']
                       /\ i''' = i'' + 1
                       /\ j''' = j'' - 1
                   ELSE
                       []
                /\ IF j'' < pivot THEN
                       i''' = i'' + 1
                    ELSE
                       []
                /\ IF arr[i'''] > pivot THEN
                       j''' = j'' - 1
                    ELSE
                       []
           INVARIANT 
               /\ i' >= lo
               /\ j' <= hi
               /\ \A k \in 0 .. lo-1 : arr[k] = arr'[k]
               /\ \A k \in hi+1 .. ArrayLen-1 : arr[k] = arr'[k]
               /\ \A k \in i' .. j' : arr'[k] \le pivot => k <= i'-1
               /\ \A k \in i' .. j' : arr'[k] > pivot => k >= j'+1
        THEN
            []
     /\ IF i' > hi THEN
            pc' = "Pop"
        ELSE
            stack' = Append(stack, <<i', hi>>)
            /\ i' = i'
            /\ j' = pivot + 1
            /\ pc' = "QS"

  \/ /\ pc = "Pop"
     /\ LET lo == IF stack = << >> THEN i ELSE FST(LAST(stack))
          hi == IF stack = << >> THEN j ELSE SND(LAST(stack)) IN
        <lo <= hi> 
        /\ IF stack # << >> THEN
               stack' = RemoveLast(stack)
               /\ i' = FST(FIRST(stack'))
               /\ j' = pivot - 1
               /\ pc' = "QS"
           ELSE
               pc' = "Done"

Spec == 
  /\ Init
  /\ [][Next]_<<pc, stack, arr, pivot, i, j, temp>>
  /\ WF_next(<<pc, stack, arr, pivot, i, j, temp>>)

Termination ==
  <>(pc = "Done")

Permutation(perm) == 
  /\ perm \in [0 .. ArrayLen-1 -> Nat]
  /\ Cardinality({perm[k] : k \in 0 .. ArrayLen-1}) = Cardinality({initArr[k] : k \in 0 .. ArrayLen-1})
  /\ \A v \in {initArr[k] : k \in 0 .. ArrayLen-1} : Cardinality({k \in 0 .. ArrayLen-1 : perm[k] = v}) = Cardinality({k \in 0 .. ArrayLen-1 : initArr[k] = v})

Sorted ==
  /\ \A k \in 0 .. ArrayLen-2 : arr[k] <= arr[k+1]

=============================================================================