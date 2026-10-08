------------------------------- MODULE QuicksortSpec -------------------------------
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS N

VARIABLES array, S, pc

Init == /\ array \in [1..N -> 1..N]
        /\ S = {[1,N]}
        /\ pc = "qs1"

PivotSelect ==
    \/ /\ pc = "qs1"
       /\ CHOOSE pivot \in 1..N : TRUE
       /\ pc' = "Partition"

Partition ==
    \/ /\ pc = "Partition"
       /\ LET left == [i \in 1..N : IF array[i] <= pivot THEN array[i] ELSE 0]
          right == [i \in 1..N : IF array[i] > pivot THEN array[i] ELSE 0]
          new_array == Append(SelectSeq(left, (left[i] /= 0)), Append([pivot], SelectSeq(right, (right[i] /= 0))))
       IN /\ array' = new_array
          /\ S' = (S \ {[l,h]}) \cup (IF l <= pivot-1 THEN {[l,pivot-1]} ELSE {}) \cup (IF pivot+1 <= h THEN {[pivot+1,h]} ELSE {})
          /\ pc' = "qs1"

Next == PivotSelect \/ Partition

Spec ==
    /\ Init
    /\ [][Next]_<<pc>>
    /\ WF_next(<<pc>>)

Termination ==
    <>[](pc = "Done")

=============================================================================