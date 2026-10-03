------------------------------- MODULE QuicksortSpec -------------------------------
VARIABLES array, S, pc

CONSTANTS N

ASSUME N \in Nat /\ N > 0

(*--algorithm quicksort
variables array = [1..N -> CHOOSE x \in 1..N: TRUE], 
          S = {1..N}, 
          pc = "qs1";

next == \/ /\ pc = "qs1"
             /\ S /= {}
             /\ \E i, j \in S : i <= j
                /\ \/ /\ i = j
                       /\ pc' = "Done"
                   \/ /\ i < j
                      /\ CHOOSE pivot \in i..j: TRUE \in i..j
                      /\ \E perm \in [i..j -> 1..N] :
                         /\ PERMUTATION(perm, array[i..j])
                         /\ \A k \in i..pivot-1 : perm[k] <= perm[pivot]
                         /\ \A k \in pivot+1..j : perm[k] >= perm[pivot]
                      /\ array' = [array EXCEPT ![k \in i..j] = perm[k]]
                      /\ S' = (S \ {i..j}) \cup ({i..pivot-1} \cap S) \cup ({pivot+1..j} \cap S)
                      /\ pc' = "qs1"
          \/ /\ pc = "Done"
             /\ pc' = "Done"

Spec == /\ PCInit
        /\ [][next]_<<array, S, pc>>
        /\ WF_next

Termination == <>(pc = "Done")

END algorithm *)
=============================================================================