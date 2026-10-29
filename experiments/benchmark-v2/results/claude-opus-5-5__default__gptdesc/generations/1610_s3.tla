---------------------------- MODULE PCalQuicksort ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT N
ASSUME NAssump == N \in Nat \ {0}

(***************************************************************************)
(* PermsOf(Arr) is the set of all permutations of the array Arr.           *)
(***************************************************************************)
PermsOf(Arr) ==
  LET Automorphisms(D) == { f \in [D -> D] : \A y \in D : \E x \in D : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { Arr ** f : f \in Automorphisms(DOMAIN Arr) }

(***************************************************************************)
(* Partitions(I, p, Arr) is the set of permutations B of Arr that leave    *)
(* every element outside the interval I unchanged and in which every       *)
(* element of B[I.lo..p] is less than or equal to every element of         *)
(* B[(p+1)..I.hi].                                                         *)
(***************************************************************************)
Partitions(I, p, Arr) ==
  { B \in PermsOf(Arr) :
      /\ \A i \in ((1..N) \ (I.lo..I.hi)) : B[i] = Arr[i]
      /\ \A i \in (I.lo..p) : \A j \in ((p+1)..I.hi) : B[i] <= B[j] }

(***************************************************************************
--algorithm QuickSort
  variables A \in [1..N -> 1..N],
            S = {[lo |-> 1, hi |-> N]};
  begin
  qs1: while S # {} do
         with I \in S do
           if I.lo < I.hi then
             with p \in I.lo..(I.hi - 1) do
               with Ap \in Partitions(I, p, A) do
                 A := Ap;
                 S := (S \ {I}) \cup { [lo |-> I.lo, hi |-> p],
                                       [lo |-> p + 1, hi |-> I.hi] }
               end with
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
        /\ S = {[lo |-> 1, hi |-> N]}
        /\ pc = "qs1"

qs1 == /\ pc = "qs1"
       /\ IF S # {}
             THEN /\ \E I \in S :
                       IF I.lo < I.hi
                          THEN /\ \E p \in I.lo..(I.hi - 1) :
                                    \E Ap \in Partitions(I, p, A) :
                                       /\ A' = Ap
                                       /\ S' = (S \ {I}) \cup
                                                 { [lo |-> I.lo, hi |-> p],
                                                   [lo |-> p + 1, hi |-> I.hi] }
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

=============================================================================