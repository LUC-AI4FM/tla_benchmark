---------------------------- MODULE QuickSort ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT N

ASSUME N \in Nat \ {0}

PermsOf(Arr) ==
  LET Automorphisms(D) == { f \in [D -> D] : \A y \in D : \E x \in D : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { Arr ** f : f \in Automorphisms(DOMAIN Arr) }

Partitions(B, piv, lo, hi) ==
  { C \in PermsOf(B) :
      /\ \A i \in (1..(lo-1)) \cup ((hi+1)..N) : C[i] = B[i]
      /\ \A i \in lo..piv, j \in (piv+1)..hi : C[i] <= C[j] }

VARIABLES Ainit, A, S, pivot, pc

vars == << Ainit, A, S, pivot, pc >>

Init == /\ Ainit \in [1..N -> 1..N]
        /\ A = Ainit
        /\ S = { <<1, N>> }
        /\ pivot = 1
        /\ pc = "qs1"

qs1 == /\ pc = "qs1"
       /\ IF S # {}
             THEN /\ \E I \in S :
                       IF I[1] < I[2]
                          THEN /\ \E piv \in I[1]..(I[2]-1) :
                                    /\ pivot' = piv
                                    /\ \E AA \in Partitions(A, piv, I[1], I[2]) :
                                          A' = AA
                                    /\ S' = (S \ {I}) \cup { <<I[1], piv>>, <<piv+1, I[2]>> }
                          ELSE /\ S' = S \ {I}
                               /\ UNCHANGED << A, pivot >>
                  /\ pc' = "qs1"
             ELSE /\ pc' = "Done"
                  /\ UNCHANGED << A, S, pivot >>
       /\ UNCHANGED Ainit

Terminating == pc = "Done" /\ UNCHANGED vars

Next == qs1 \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

=============================================================================