------------------------------ MODULE Quicksort ------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N > 0

VARIABLES A, S, pc

vars == <<A, S, pc>>

(* Helper: the set of all permutations of a sequence *)
Perms(seq) ==
    LET Domain == 1..Len(seq)
        Bijections == {f \in [Domain -> Domain] : \A i, j \in Domain : i # j => f[i] # f[j]}
    IN {[i \in Domain |-> seq[f[i]]] : f \in Bijections}

(* Helper: check if array arr satisfies partition property around pivot position p in interval [lo, hi] *)
IsPartitioned(arr, lo, hi, p) ==
    /\ \A i \in lo..(p-1) : arr[i] <= arr[p]
    /\ \A j \in (p+1)..hi : arr[j] >= arr[p]

(* Initial state *)
Init ==
    /\ A \in [1..N -> 1..N]
    /\ S = {<<1, N>>}
    /\ pc = "qs1"

(* Main quicksort action at control location qs1 *)
qs1 ==
    /\ pc = "qs1"
    /\ IF S = {}
       THEN /\ pc' = "Done"
            /\ A' = A
            /\ S' = S
       ELSE \E interval \in S :
            LET lo == interval[1]
                hi == interval[2]
            IN
            /\ IF lo >= hi
               THEN (* Trivial interval, just remove it *)
                    /\ S' = S \ {interval}
                    /\ A' = A
                    /\ pc' = "qs1"
               ELSE (* Non-trivial interval: pick pivot, partition *)
                    \E p \in lo..hi :  (* Nondeterministically select pivot position *)
                    \E newA \in Perms(A) :  (* Nondeterministically select a permutation *)
                        (* The permutation must only change the interval [lo, hi] *)
                        /\ \A i \in 1..N : (i < lo \/ i > hi) => newA[i] = A[i]
                        (* The subarray [lo, hi] in newA is a permutation of [lo, hi] in A *)
                        /\ {newA[i] : i \in lo..hi} = {A[i] : i \in lo..hi}
                        (* The partition property must hold *)
                        /\ IsPartitioned(newA, lo, hi, p)
                        (* Update state *)
                        /\ A' = newA
                        /\ S' = (S \ {interval}) \cup 
                                (IF p > lo THEN {<<lo, p-1>>} ELSE {}) \cup
                                (IF p < hi THEN {<<p+1, hi>>} ELSE {})
                        /\ pc' = "qs1"

(* Done state - stuttering *)
Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

(* Next-state relation *)
Next == qs1 \/ Done

(* Specification with weak fairness *)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(* Safety invariant: type correctness *)
TypeInvariant ==
    /\ A \in [1..N -> 1..N]
    /\ S \subseteq {<<i, j>> : i \in 1..N, j \in 1..N}
    /\ pc \in {"qs1", "Done"}

(* Liveness property: eventual termination *)
Termination == <>(pc = "Done")

=============================================================================