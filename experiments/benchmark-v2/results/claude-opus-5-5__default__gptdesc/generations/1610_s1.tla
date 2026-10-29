---------------------------- MODULE QuickSort ----------------------------
EXTENDS Integers

CONSTANT N

ASSUME N \in Nat

(***************************************************************************)
(* PermsOf(Arr) is the set of all permutations of the array Arr.           *)
(***************************************************************************)
PermsOf(Arr) ==
  LET Automorphisms(D) == { f \in [D -> D] : \A y \in D : \E x \in D : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { Arr ** f : f \in Automorphisms(DOMAIN Arr) }

(***************************************************************************)
(* Partitions(B, pivot, lo, hi) is the set of permutations C of B that     *)
(* leave elements outside lo..hi unchanged and such that every element in  *)
(* lo..pivot is less than or equal to every element in (pivot+1)..hi.      *)
(***************************************************************************)
Partitions(B, pivot, lo, hi) ==
  { C \in PermsOf(B) :
      /\ \A i \in (1..(lo-1)) \cup ((hi+1)..N) : C[i] = B[i]
      /\ \A i \in lo..pivot, j \in (pivot+1)..hi : C[i] =< C[j] }

(***************************************************************************
--algorithm QuickSort
variables A \in [1..N -> 1..N],
          S = {<<1, N>>};
begin
qs1: while S # {} do
       with I \in S do
         if I[1] < I[2] then
           with p \in I[1]..(I[2]-1),
                P \in Partitions(A, p, I[1], I[2]) do
             A := P;
             S := (S \ {I}) \cup {<<I[1], p>>, <<p+1, I[2]>>}
           end with
         else
           S := S \ {I}
         end if
       end with
     end while
end algorithm
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES A, S, pc

vars == << A, S, pc >>

Init == /\ A \in [1..N -> 1..N]
        /\ S = {<<1, N>>}
        /\ pc = "qs1"

qs1 == /\ pc = "qs1"
       /\ IF S # {}
             THEN /\ \E I \in S :
                       IF I[1] < I[2]
                          THEN /\ \E p \in I[1]..(I[2]-1) :
                                    \E P \in Partitions(A, p, I[1], I[2]) :
                                       /\ A' = P
                                       /\ S' = (S \ {I}) \cup {<<I[1], p>>, <<p+1, I[2]>>}
                          ELSE /\ S' = S \ {I}
                               /\ A' = A
                  /\ pc' = "qs1"
             ELSE /\ pc' = "Done"
                  /\ UNCHANGED << A, S >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == qs1
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")
\* END TRANSLATION

(***************************************************************************)
(* Additional safety properties.                                           *)
(***************************************************************************)
TypeOK == /\ A \in [1..N -> 1..N]
          /\ S \subseteq ((1..N+1) \X (0..N))
          /\ pc \in {"qs1", "Done"}

Sorted == pc = "Done" => \A i, j \in 1..N : i < j => A[i] =< A[j]
=============================================================================