------------------------------- MODULE QuicksortSpec -------------------------------

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS N

VARIABLES array, S, pc

Init == /\ array \in [1..N -> 1..N]
        /\ S = {[1..N]}
        /\ pc = "qs1"

PivotSelect ==
    CHOOSE pivot \in DOMAIN array : TRUE

Partition ==
    LET pivotVal == array[pivot]
        leftSeq == << a \in SUBSEQ(array) : a <= pivotVal >>
        rightSeq == << a \in SUBSEQ(array) : a > pivotVal >>
    IN
        /\ array' = (leftSeq \o [len(leftSeq)+1] <- pivotVal \o rightSeq)
        /\ S' = (S \ {[lo..hi]})
        /\ IF len(leftSeq) > 1 THEN S' \cup {[1..len(leftSeq)]}
           ELSE S'
        /\ IF len(rightSeq) > 1 THEN S' \cup {[len(leftSeq)+2..len(array)]}
           ELSE S'

qs1 ==
    \/ pc = "qs1" /\ S /= {} ->
         LET [lo..hi] \in S
             pivot \in [lo..hi]
         IN
         /\ (pivot \in [lo..hi])
         /\ array' = array
         /\ S' = S
         /\ pc' = "Partition"
    \/ pc = "qs1" /\ S = {} -> 
         /\ array' = array
         /\ S' = S
         /\ pc' = "Done"

Next ==
    qs1 \/ Partition

Spec ==
    /\ Init
    /\ [][ Next ]_<<array, S, pc>>
    /\ WF_next(Next)

Termination == <>[] (pc = "Done")

=============================================================================