---- MODULE MergeSort ----
EXTENDS Integers, Sequences, TLC

CONSTANTS N, ArrayLen

VARIABLES pc, stack, a, b, len, left, right, mid, i, j, k

vars == <<pc, stack, a, b, len, left, right, mid, i, j, k>>

IsSorted(seq, l) == \A idx \in 1..(l-1) : seq[idx] <= seq[idx+1]

Init ==
    /\ \E l \in 1..ArrayLen :
        /\ len = l
        /\ \E arr \in [1..l -> 1..N] : a = arr
    /\ b = [x \in 1..len |-> 0]
    /\ pc = "Sort"
    /\ stack = << >>
    /\ left = 1
    /\ right = len
    /\ mid = 0
    /\ i = 0
    /\ j = 0
    /\ k = 0

(* The logic for returning from a procedure call *)
Return ==
    /\ IF stack = << >>
       THEN /\ pc' = "Done"
            /\ UNCHANGED <<stack, a, b, len, left, right, mid, i, j, k>>
       ELSE /\ LET frame == Head(stack) IN
                /\ pc' = frame.pc
                /\ left' = frame.left
                /\ right' = frame.right
                /\ mid' = frame.mid
                /\ stack' = Tail(stack)
                /\ UNCHANGED <<a, b, len, i, j, k>>

(* Main mergesort procedure entry. If [left, right] is not a base case,
   it pushes the context for the second recursive call and the merge step
   onto the stack, then makes the first recursive call. If it is a base
   case, it returns. *)
Sort ==
    /\ pc = "Sort"
    /\ IF left < right
       THEN /\ LET mid_new == left + (right - left) \div 2
            IN
            /\ stack' = << [ left |-> left, right |-> right, mid |-> mid_new, pc |-> "Sort2" ] >> \o stack
            /\ pc' = "Sort"
            /\ left' = left
            /\ right' = mid_new
            /\ mid' = mid_new
            /\ UNCHANGED <<a, b, len, i, j, k>>
       ELSE /\ Return

(* After the first recursive call returns, this action sets up for the
   second recursive call. It pushes the context for the merge step
   onto the stack. *)
Sort2 ==
    /\ pc = "Sort2"
    /\ stack' = << [ left |-> left, right |-> right, mid |-> mid, pc |-> "Merge" ] >> \o stack
    /\ pc' = "Sort"
    /\ left' = mid + 1
    /\ right' = right
    /\ UNCHANGED <<a, b, len, mid, i, j, k>>

(* After the second recursive call returns, this action starts the merge
   procedure. It copies the relevant subarray from `a` to the buffer `b`
   and initializes the loop counters. *)
Merge ==
    /\ pc = "Merge"
    /\ b' = [idx \in 1..len |-> IF idx >= left /\ idx <= right THEN a[idx] ELSE b[idx]]
    /\ i' = left
    /\ j' = mid + 1
    /\ k' = left
    /\ pc' = "MergeLoop"
    /\ UNCHANGED <<stack, a, len, left, right, mid>>

(* The main loop of the merge procedure. It compares elements from the
   two halves in the buffer `b` and copies the smaller one back to `a`. *)
MergeLoop ==
    /\ pc = "MergeLoop"
    /\ IF i <= mid /\ j <= right
       THEN /\ IF b[i] <= b[j]
               THEN /\ a' = [a EXCEPT ![k] = b[i]]
                    /\ i' = i + 1
                    /\ UNCHANGED j
               ELSE /\ a' = [a EXCEPT ![k] = b[j]]
                    /\ j' = j + 1
                    /\ UNCHANGED i
            /\ k' = k + 1
            /\ pc' = "MergeLoop"
            /\ UNCHANGED <<stack, b, len, left, right, mid>>
       ELSE /\ pc' = "MergeCopyLeft"
            /\ UNCHANGED <<stack, a, b, len, left, right, mid, i, j, k>>

(* After the main merge loop, this action copies any remaining elements
   from the left half. *)
MergeCopyLeft ==
    /\ pc = "MergeCopyLeft"
    /\ IF i <= mid
       THEN /\ a' = [a EXCEPT ![k] = b[i]]
            /\ i' = i + 1
            /\ k' = k + 1
            /\ pc' = "MergeCopyLeft"
            /\ UNCHANGED <<stack, b, len, left, right, mid, j>>
       ELSE /\ pc' = "MergeCopyRight"
            /\ UNCHANGED <<stack, a, b, len, left, right, mid, i, j, k>>

(* After copying the left half, this action copies any remaining elements
   from the right half. *)
MergeCopyRight ==
    /\ pc = "MergeCopyRight"
    /\ IF j <= right
       THEN /\ a' = [a EXCEPT ![k] = b[j]]
            /\ j' = j + 1
            /\ k' = k + 1
            /\ pc' = "MergeCopyRight"
            /\ UNCHANGED <<stack, b, len, left, right, mid, i>>
       ELSE /\ pc' = "MergeEnd"
            /\ UNCHANGED <<stack, a, b, len, left, right, mid, i, j, k>>

(* The end of the merge procedure, which signifies the end of a mergesort
   call. This action returns from the call. *)
MergeEnd ==
    /\ pc = "MergeEnd"
    /\ Return

Next ==
    \/ Sort
    \/ Sort2
    \/ Merge
    \/ MergeLoop
    \/ MergeCopyLeft
    \/ MergeCopyRight
    \/ MergeEnd

Spec == Init /\ [][Next]_vars

(* Safety property: When the algorithm is done, the array is sorted. *)
SortedAtEnd == pc = "Done" => IsSorted(a, len)

(* Liveness property: The algorithm eventually terminates. *)
Termination == <>(pc = "Done")

=============================================================================