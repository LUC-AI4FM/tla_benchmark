------------------------------ MODULE Quicksort ------------------------------

EXTENDS Naturals, Integers

CONSTANT N

VARIABLES A, S, A0

Index == 1..N
Values == 1..N

Pairs == { p \in (Index \X Index) : p[1] < p[2] }

IsInjective(f) ==
  \A x \in DOMAIN f: \A y \in DOMAIN f: x # y => f[x] # f[y]

Bij(L, f) ==
  /\ f \in [L -> L]
  /\ IsInjective(f)
  /\ f[L] = L

PermOn(A, B, L) ==
  \E pi \in [L -> L]:
    /\ Bij(L, pi)
    /\ \A i \in L: B[i] = A[pi[i]]

PermTotal(a, a0) ==
  \E pi \in [Index -> Index]:
    /\ Bij(Index, pi)
    /\ \A i \in Index: a[i] = a0[pi[i]]

Sorted(a) ==
  \A i \in Index: \A j \in Index: i <= j => a[i] <= a[j]

PartitionOK(a, l, h, k) ==
  \A i \in l..(k-1): \A j \in (k+1)..h: a[i] <= a[j]

Partitioned(Aold, Anew, l, h, k) ==
  LET L == l..h IN
    /\ k \in L
    /\ \A i \in (Index \ L): Anew[i] = Aold[i]
    /\ PermOn(Aold, Anew, L)
    /\ PartitionOK(Anew, l, h, k)

Init ==
  /\ A \in [Index -> Values]
  /\ A0 = A
  /\ S = IF N <= 1 THEN {} ELSE {<<1, N>>}

Next ==
  /\ S # {}
  /\ \E p \in S:
        LET l == p[1] IN
        LET h == p[2] IN
        \E k \in l..h:
        \E Anew \in [Index -> Values]:
          /\ Partitioned(A, Anew, l, h, k)
          /\ A' = Anew
          /\ S' =
               (S \ {p})
               \cup (IF l < k-1 THEN {<<l, k-1>>} ELSE {})
               \cup (IF k+1 < h THEN {<<k+1, h>>} ELSE {})
  /\ A0' = A0

vars == << A, S, A0 >>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Done == S = {}

Safety == [](Done => (Sorted(A) /\ PermTotal(A, A0)))

Termination == <> Done

=============================================================================