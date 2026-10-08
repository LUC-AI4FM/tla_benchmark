------------------------------ MODULE QuickSort ------------------------------
EXTENDS Naturals, Sequences

(*--------------------------------------------------------------------------*)
(* CONSTANTS *)
CONSTANTS N

(*--------------------------------------------------------------------------*)
(* VARIABLES *)
VARIABLE A, I

(*--------------------------------------------------------------------------*)
(* Helper predicates *)

(* Permutation predicate:  A2 is a permutation of A1 on [l,r] with pivot p fixed. *)
Permutation(A1, A2, l, r, p) ==
  /\ \A i \in 1..N : (i < l \/ i > r) => A1[i] = A2[i]
  /\ \E f \in [l..r -> l..r] :
        /\ \A i \in l..r : f[i] \in l..r
        /\ \A i,j \in l..r : (i /= j) => f[i] /= f[j]
        /\ f[p] = p
        /\ \A i \in l..r : A2[i] = A1[f[i]]

(* Partition condition: every element left of pivot <= every element right of pivot. *)
PartitionCondition(A, l, r, p) ==
  \A i,j \in l..r :
    (i <= p-1 /\ j >= p+1) => A[i] <= A[j]

(* Full partition predicate: array after a valid partition step. *)
Partition(A1, A2, l, r, p) ==
  /\ Permutation(A1, A2, l, r, p)
  /\ PartitionCondition(A2, l, r, p)

(*--------------------------------------------------------------------------*)
(* Initial state *)

Init == 
  /\ A \in [1..N -> 1..N]
  /\ I = { <<1,N>> }

(*--------------------------------------------------------------------------*)
(* Next-state relation *)

Next ==
  \E i \in I :
    LET l = i[1], r = i[2] IN
      IF r - l + 1 <= 1 THEN
        /\ A' = A
        /\ I' = I \ {i}
      ELSE
        \E p \in 1..N : (p >= l /\ p <= r) /\
          Partition(A, A', l, r, p) /\
          I' = (I \ {i}) \cup { <<l,p-1>>, <<p+1,r>> }

(*--------------------------------------------------------------------------*)
(* Specification *)

Spec == Init /\ [][Next]_<<A,I>>

(*--------------------------------------------------------------------------*)
(* Liveness property: the algorithm eventually terminates. *)
Termination == []<>(I = {})

=============================================================================