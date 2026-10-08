------------------------------ MODULE Quicksort ------------------------------
EXTENDS Integers, FiniteSets

CONSTANT N
ASSUME N \in Nat /\ N >= 1

VARIABLES A, S

Indices == 1..N

Terminated == S = {}

PermOnSegment(A, B, l, r) ==
  /\ B \in [Indices -> Indices]
  /\ \A k \in (Indices \ (l..r)) : B[k] = A[k]
  /\ \A v \in Indices :
        Cardinality({ i \in (l..r) : A[i] = v }) =
        Cardinality({ i \in (l..r) : B[i] = v })

PartitionCond(B, l, p, r) ==
  /\ p \in l..r
  /\ \A i \in l..(p - 1) : \A j \in p..r : B[i] <= B[j]

Init ==
  /\ A \in [Indices -> Indices]
  /\ S = {<<1, N>>}

Partition ==
  \E l, r \in Indices :
    /\ <<l, r>> \in S
    /\ l < r
    /\ \E p \in l..r :
       \E B \in [Indices -> Indices] :
         /\ PermOnSegment(A, B, l, r)
         /\ PartitionCond(B, l, p, r)
         /\ A' = B
         /\ S' = (S \ {<<l, r>>})
                 \cup (IF l <= p - 1 THEN {<<l, p - 1>>} ELSE {})
                 \cup (IF p + 1 <= r THEN {<<p + 1, r>>} ELSE {})

Remove ==
  \E l, r \in Indices :
    /\ <<l, r>> \in S
    /\ l = r
    /\ A' = A
    /\ S' = S \ {<<l, r>>}

Next == Partition \/ Remove

vars == <<A, S>>

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>Terminated
=============================================================================