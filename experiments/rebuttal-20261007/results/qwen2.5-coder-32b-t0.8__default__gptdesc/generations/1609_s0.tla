------------------------------- MODULE QuicksortSpec -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS ArrayLen

VARIABLES pc, stack, pivot, arr, left, right

Init == 
    /\ pc = "Start"
    /\ stack = << >> 
    /\ arr \in [1..ArrayLen -> Nat]
    /\ left = 1
    /\ right = ArrayLen

QS ==
    \/ /\ pc = "Start"
       /\ UNCHANGED stack
       /\ UNCHANGED pivot
       /\ UNCHANGED arr
       /\ UNCHANGED left
       /\ UNCHANGED right
       /\ pc' = "ChoosePivot"

    \/ /\ pc = "ChoosePivot"
       /\ left <= right
       /\ pivot \in {left .. right}
       /\ pc' = "Partition"

    \/ /\ pc = "ChoosePivot"
       /\ left > right
       /\ pc' = "Return"

    \/ /\ pc = "Partition"
       /\ LET lstart == left
          rstart == right
          pval == arr[pivot]
      IN \/ /\ /\ EXISTS i \in {lstart .. pivot-1} : arr[i] > pval \/ EXISTS j \in {pivot+1 .. rstart} : arr[j] <= pval
             /\ LET new_arr == [arr EXCEPT ![lstart] = IF arr[lstart] > pval THEN arr[pivot] ELSE arr[lstart],
                                           ![pivot] = arr[lstart]]
                IN \/ /\ lstart' = lstart + 1
                   /\ pivot' = IF arr[lstart] > pval THEN lstart ELSE pivot
                   /\ arr' = new_arr
                   /\ pc' = "Partition"
                   /\ UNCHANGED stack
                   /\ UNCHANGED right

             [] /\ EXISTS i \in {pivot+1 .. rstart} : arr[i] <= pval \/ EXISTS j \in {lstart .. pivot-1} : arr[j] > pval
                /\ LET new_arr == [arr EXCEPT ![rstart] = IF arr[rstart] <= pval THEN arr[pivot] ELSE arr[rstart],
                                           ![pivot] = arr[rstart]]
                IN \/ /\ rstart' = rstart - 1
                   /\ pivot' = IF arr[rstart] <= pval THEN rstart ELSE pivot
                   /\ arr' = new_arr
                   /\ pc' = "Partition"
                   /\ UNCHANGED stack
                   /\ UNCHANGED left

             [] /\ \A i \in {lstart .. pivot-1} : arr[i] <= pval /\ \A j \in {pivot+1 .. rstart} : arr[j] > pval
                /\ lstart' = pivot + 1
                /\ rstart' = pivot - 1
                /\ pc' = "CallQS"

    \/ /\ pc = "CallQS"
       /\ left <= right
       /\ stack' = Append(stack, <<pivot+1, right>>)
       /\ left' = lstart
       /\ right' = pivot-1
       /\ pc' = "Start"

    \/ /\ pc = "CallQS"
       /\ left > right
       /\ pc' = "Return"

    \/ /\ pc = "Return"
       /\ stack # << >>
       /\ LET frame == Head(stack)
          new_left == Elem(frame, 1)
          new_right == Elem(frame, 2)
      IN /\ stack' = Tail(stack)
         /\ left' = new_left
         /\ right' = new_right
         /\ pc' = "Start"

    \/ /\ pc = "Return"
       /\ stack = << >>
       /\ pc' = "Done"

Next ==
    QS

Spec == 
    /\ Init
    /\ [][Next]_<<pc, stack, pivot, arr, left, right>>
    /\ WF_[Next]_<<pc, stack, pivot, arr, left, right>>

Termination == <>[](pc = "Done")

Sorted ==
    \A i \in 1..ArrayLen-1 : arr[i] <= arr[i+1]

Permutation ==
    \E initial_arr \in [1..ArrayLen -> Nat]:
        /\ initial_arr = [1..ArrayLen -> arr]
        /\ PERMUTATION({arr[i]: i \in 1..ArrayLen}, {initial_arr[i]: i \in 1..ArrayLen})

Test == 
    /\ Termination
    /\ Sorted
    /\ Permutation

=============================================================================