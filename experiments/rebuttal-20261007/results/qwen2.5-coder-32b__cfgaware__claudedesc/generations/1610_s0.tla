------------------------------- MODULE QuickSort -------------------------------

CONSTANTS N

VARIABLES Ainit, A, S, pivot, pc

(*--algorithm Quicksort
variables Ainit = [1..N -> ?], A = Ainit, S = {<<1, N>>}, pivot \in 1..N, pc = "Init";

next == 
    /\ pc = "Init"
    /\ pc' = "qs1"

qs1 ==
    \/ /\ S /= {}
       /\ CHOOSE I \in S: TRUE
       /\ (/\ I[2] - I[1] > 0
           /\ pivot \in I[1]..I[2]
           /\ A' = [j \in 1..N -> IF j \notin I[1]..I[2] THEN A[j] ELSE CHOOSE v \in SUBSET {A[k]: k \in I[1]..I[2]}: TRUE]
           /\ (\A x \in {A'[k]: k \in I[1]..pivot-1}, y \in {A'[k]: k \in pivot+1..I[2]}: x <= y)
           /\ S' = (S \ {I}) \cup {<<I[1], pivot-1>>, <<pivot+1, I[2]>>})
       \/ /\ I[2] - I[1] <= 0
          /\ S' = S \ {I}
    \/ /\ S = {}
       /\ pc' = "Done"

end algorithm *)

Init == 
    /\ Ainit \in [1..N -> 1..N]
    /\ A = Ainit
    /\ S = {<<1, N>>}
    /\ pivot \in 1..N
    /\ pc = "Init"

Next ==
    \/ pc = "Init" /\ qs1
    \/ pc = "qs1" /\ qs1

Spec == Init /\ [][Next]_<<Ainit, A, S, pivot, pc>>

Termination == <>(pc = "Done")

=============================================================================