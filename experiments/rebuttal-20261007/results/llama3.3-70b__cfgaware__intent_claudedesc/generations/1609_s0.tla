---------------------------- MODULE Quicksort ----------------------------
EXTENDS Integers, Sequences

CONSTANT ArrayLen

VARIABLE arr, pc

Init == (* Initialize array nondeterministically *)
        /\ arr \in [1..ArrayLen -> 1..ArrayLen]
        /\ pc = 1

Next == (* Choose a subarray range and partition it *)
        /\ pc <= ArrayLen
        /\ \E pivot \in {pc..ArrayLen} :
            /\ arr' = [arr EXCEPT !i \in {pc..ArrayLen} : 
                        IF i < pivot THEN arr[i] <= arr[pivot] ELSE arr[i] > arr[pivot]]
            /\ pc' = IF pivot < ArrayLen THEN pivot + 1 ELSE ArrayLen + 1
        /\ UNCHANGED << >>

Spec == Init /\ [][Next]_<<arr, pc>>

Termination == <>[pc = ArrayLen + 1]_pc

THEOREM Spec => []Termination
THEOREM Spec => [](arr \in SortedSeqs(1..ArrayLen))
=============================================================================