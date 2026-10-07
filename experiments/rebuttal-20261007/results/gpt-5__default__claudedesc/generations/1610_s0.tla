------------------------------ MODULE NondetQuickSort ------------------------------

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat \ {0}

VARIABLES Ainit, A, S, pivot, pc

vars == << Ainit, A, S, pivot, pc >>

Indices(i, j) == i..j

IsBij(pi, S) ==
  /\ pi \in [S -> S]
  /\ \A x \in S: \A y \in S: (pi[x] = pi[y]) => x = y
  /\ \A z \in S: \E x \in S: pi[x] = z

PermutationRange(A, A2, i, j) ==
  LET R == Indices(i, j) IN
    \E pi \in [R -> R]:
      /\ IsBij(pi, R)
      /\ \A k \in R: A2[k] = A[pi[k]]
      /\ \A k \in (1..N) \ R: A2[k] = A[k]

PartitionOK(A2, i, j, piv) ==
  \A l \in Indices(i, piv):
    \A r \in Indices(piv + 1, j):
      A2[l] <= A2[r]

Init ==
  /\ Ainit \in [1..N -> 1..N]
  /\ A = Ainit
  /\ S = {<<1, N>>}
  /\ pivot = 0
  /\ pc = "Run"

qs1 ==
  /\ pc = "Run"
  /\ S # {}
  /\ \E I \in S:
       LET i == I[1] IN
       LET j == I[2] IN
         IF i = j THEN
           /\ A' = A
           /\ Ainit' = Ainit
           /\ S' = S \ {I}
           /\ pivot' = pivot
           /\ pc' = "Run"
         ELSE
           \E piv \in i..j:
             \E Anew \in [1..N -> 1..N]:
               /\ PermutationRange(A, Anew, i, j)
               /\ PartitionOK(Anew, i, j, piv)
               /\ A' = Anew
               /\ Ainit' = Ainit
               /\ S' = (S \ {I})
                      \cup (IF i <= piv - 1 THEN {<<i, piv - 1>>} ELSE {})
                      \cup (IF piv + 1 <= j THEN {<<piv + 1, j>>} ELSE {})
               /\ pivot' = piv
               /\ pc' = "Run"

done ==
  /\ pc = "Run"
  /\ S = {}
  /\ A' = A
  /\ Ainit' = Ainit
  /\ S' = S
  /\ pivot' = pivot
  /\ pc' = "Done"

Next == qs1 \/ done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <> (pc = "Done")

==============================