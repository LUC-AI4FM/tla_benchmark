------------------------------- MODULE Quicksort -------------------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS N

VARIABLES arr, intervals

Permutation(seq) == /\ seq \in Seq(1..N)
                   /\ Cardinality({seq[i] : i \in DOMAIN seq}) = N
                   /\ \A x \in 1..N: x \in {seq[i] : i \in DOMAIN seq}

Init == /\ arr \in Seq(1..N) 
        /\ intervals = {[1:N]}

Next ==
    \/ /\ intervals /= {}
       /\ CHOOSE interval \in intervals:
            LET pivot \in INTERVALS(interval)[2] BE
                /\ \E perm \in Permutation(arr):
                    /\ \A i \notin interval: perm[i] = arr[i]
                    /\ \A i \in interval: perm[i] \le perm[pivot]
                       \/ i > pivot
                   /\ arr' = perm
                   /\ intervals' = (intervals \ {interval}) 
                                  \cup {[Fst(interval):pivot-1], [pivot+1:Snd(interval)]}
    \/ /\ intervals = {}
       /\ UNCHANGED <<arr, intervals>>

Spec == Init /\ [][Next]_<<arr, intervals>> /\ WF_next(<<arr, intervals>>)

THEOREM Spec => <>[](intervals = {})

=============================================================================