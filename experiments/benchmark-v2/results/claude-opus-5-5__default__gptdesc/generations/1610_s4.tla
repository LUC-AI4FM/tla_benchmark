------------------------------- MODULE QuickSort -------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT N
ASSUME N \in Nat

PermsOf(Arr) ==
  LET Automorphisms(D) == { f \in [D -> D] :
                              \A y \in D : \E x \in D : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { Arr ** f : f \in Automorphisms(DOMAIN Arr) }

Max(T) == CHOOSE x \in T : \A y \in T : x >= y
Min(T) == CHOOSE x \in T : \A y \in T : x =< y

Partitions(I, p, Arr) ==
  { B \in PermsOf(Arr) :
      /\ \A i \in (1..N) \ I : B[i] = Arr[i]
      /\ \A i \in I : \A j \in I : (i =< p) /\ (p < j) => (B[i] =< B[j]) }

(* --algorithm QuickSort
variables A \in [1..N -> 1..N], S = {1..N};
begin
qs1: while S # {} do
       with I \in S do
         if Cardinality(I) = 1 then
           S := S \ {I};
         else
           with p \in Min(I) .. (Max(I) - 1),
                P \in Partitions(I, p, A) do
             A := P;
             S := (S \ {I}) \cup {Min(I)..p, (p+1)..Max(I)}
           end with;
         end if;
       end with;
     end while;
end algorithm
*)

\* BEGIN TRANSLATION
VARIABLES A, S, pc

vars == << A, S, pc >>

Init == /\ A \in [1..N -> 1..N]
        /\ S = {1..N}
        /\ pc = "qs1"

qs1 == /\ pc = "qs1"
       /\ IF S # {}
             THEN /\ \E I \in S :
                       IF Cardinality(I) = 1
                          THEN /\ S' = S \ {I}
                               /\ A' = A
                          ELSE /\ \E p \in Min(I) .. (Max(I) - 1) :
                                    \E P \in Partitions(I, p, A) :
                                       /\ A' = P
                                       /\ S' = (S \ {I}) \cup {Min(I)..p, (p+1)..Max(I)}
                  /\ pc' = "qs1"
             ELSE /\ pc' = "Done"
                  /\ UNCHANGED << A, S >>

Next == qs1
           \/ (pc = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

TypeOK == /\ A \in [1..N -> 1..N]
          /\ S \subseteq SUBSET (1..N)
          /\ pc \in {"qs1", "Done"}

=============================================================================