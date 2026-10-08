------------------------------ MODULE NondetQuickSort ------------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANT N

VARIABLES Ainit, A, S, pivot, pc

vars == << Ainit, A, S, pivot, pc >>

Range(I) == I[1]..I[2]

IsBijection(f, S) ==
  /\ f \in [S -> S]
  /\ \A x \in S: \A y \in S: (f[x] = f[y]) => x = y
  /\ \A y \in S: \E x \in S: f[x] = y

PermuteOn(A, Ap, I) ==
  LET D == Range(I) IN
  /\ \A k \in (1..N) \ D: Ap[k] = A[k]
  /\ \E f \in [D -> D]:
       /\ IsBijection(f, D)
       /\ \A k \in D: Ap[k] = A[f[k]]

Partitioned(Ap, I, piv) ==
  /\ I[1] <= piv
  /\ piv < I[2]
  /\ \A i \in (I[1]..piv):
       \A j \in ((piv + 1)..I[2]): Ap[i] <= Ap[j]

Init ==
  /\ N \in Nat
  /\ N >= 1
  /\ Ainit \in [1..N -> 1..N]
  /\ A = Ainit
  /\ S = {<<1, N>>}
  /\ pivot = 0
  /\ pc = "qs1"

qs1 ==
  /\ pc = "qs1"
  /\ S /= {}
  /\ \E I \in S:
        IF I[1] = I[2] THEN
          /\ A' = A
          /\ Ainit' = Ainit
          /\ pivot' = pivot
          /\ S' = S \ {I}
          /\ pc' = "qs1"
        ELSE
          /\ \E piv \in I[1]..(I[2] - 1):
               /\ \E Ap \in [1..N -> 1..N]:
                    /\ PermuteOn(A, Ap, I)
                    /\ Partitioned(Ap, I, piv)
                    /\ A' = Ap
                    /\ Ainit' = Ainit
                    /\ pivot' = piv
                    /\ LET left == <<I[1], piv>>
                           right == <<piv + 1, I[2]>>
                       IN S' = (S \ {I}) \cup { K \in {left, right} : K[1] < K[2] }
                    /\ pc' = "qs1"

Done ==
  /\ pc = "qs1"
  /\ S = {}
  /\ A' = A
  /\ Ainit' = Ainit
  /\ pivot' = pivot
  /\ S' = S
  /\ pc' = "Done"

Next == qs1 \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <> (pc = "Done")

=============================================================================