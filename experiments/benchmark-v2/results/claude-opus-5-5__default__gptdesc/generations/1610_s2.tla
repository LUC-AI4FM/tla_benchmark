---------------------------- MODULE QuickSort ----------------------------
EXTENDS Integers

CONSTANT N

ASSUME N \in Nat

PermsOf(Arr) ==
  LET Automorphisms(D) == { f \in [D -> D] : \A y \in D : \E x \in D : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { Arr ** f : f \in Automorphisms(DOMAIN Arr) }

(***************************************************************************
--algorithm QuickSort
variables A \in [1..N -> 1..N], S = {<<1, N>>};
begin
qs1: while S # {} do
       with I \in S do
         if I[1] < I[2] then
           with p \in I[1] .. (I[2]-1) do
             with Ap \in { AA \in PermsOf(A) :
                             (\A i \in 1..(I[1]-1) : AA[i] = A[i])
                          /\ (\A i \in (I[2]+1)..N : AA[i] = A[i])
                          /\ (\A i \in I[1]..p : \A j \in (p+1)..I[2] :
                                 AA[i] =< AA[j]) } do
               A := Ap;
               S := (S \ {I}) \cup {<<I[1], p>>, <<p+1, I[2]>>}
             end with
           end with
         else S := S \ {I}
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
                          THEN \E p \in I[1] .. (I[2]-1) :
                                 \E Ap \in { AA \in PermsOf(A) :
                                                (\A i \in 1..(I[1]-1) : AA[i] = A[i])
                                             /\ (\A i \in (I[2]+1)..N : AA[i] = A[i])
                                             /\ (\A i \in I[1]..p : \A j \in (p+1)..I[2] :
                                                    AA[i] =< AA[j]) } :
                                   /\ A' = Ap
                                   /\ S' = (S \ {I}) \cup {<<I[1], p>>, <<p+1, I[2]>>}
                          ELSE /\ S' = S \ {I}
                               /\ A' = A
                  /\ pc' = "qs1"
             ELSE /\ pc' = "Done"
                  /\ UNCHANGED << A, S >>

Terminating == pc = "Done" /\ UNCHANGED vars

Next == qs1 \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")
\* END TRANSLATION

TypeOK == /\ A \in [1..N -> 1..N]
          /\ S \subseteq ((1..(N+1)) \X (0..N))
          /\ pc \in {"qs1", "Done"}

=============================================================================