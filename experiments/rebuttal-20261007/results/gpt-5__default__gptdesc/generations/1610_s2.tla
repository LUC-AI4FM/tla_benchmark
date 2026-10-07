---- MODULE QuicksortPlusCalTranslation ----
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat

VARIABLES A, S, pc, A0

vars == << A, S, pc, A0 >>

Segment(l, r) == IF l <= r THEN l..r ELSE {}

Intervals == { i \in [l: 1..N, r: 1..N] : i.l <= i.r }

IsPermOn(pi, I) ==
  /\ pi \in [I -> I]
  /\ { pi[i] : i \in I } = I

PermWithin(A, B, I) ==
  /\ \A j \in (1..N) \ I: B[j] = A[j]
  /\ \E pi \in [I -> I]:
       /\ IsPermOn(pi, I)
       /\ \A i \in I: B[i] = A[pi[i]]

PartitionOK(A, B, l, p, r) ==
  /\ PermWithin(A, B, Segment(l, r))
  /\ \A i \in l..(p-1): B[i] <= B[p]
  /\ \A i \in (p+1)..r: B[i] >= B[p]

LeftSet(seg, p) ==
  IF seg.l < p THEN { [l |-> seg.l, r |-> p-1] } ELSE {}

RightSet(seg, p) ==
  IF p < seg.r THEN { [l |-> p+1, r |-> seg.r] } ELSE {}

IsFullPerm(X, Y) ==
  \E pi \in [1..N -> 1..N]:
    /\ IsPermOn(pi, 1..N)
    /\ \A i \in 1..N: X[i] = Y[pi[i]]

Init ==
  /\ A \in [1..N -> 1..N]
  /\ A0 = A
  /\ S = IF N >= 1 THEN { [l |-> 1, r |-> N] } ELSE {}
  /\ pc = "qs1"

qs1 ==
  /\ pc = "qs1"
  /\ \/ /\ S = {}
        /\ pc' = "Done"
        /\ UNCHANGED << A, S, A0 >>
     \/ \E seg \in S, p \in seg.l..seg.r, B \in [1..N -> 1..N]:
          /\ PartitionOK(A, B, seg.l, p, seg.r)
          /\ A' = B
          /\ S' = (S \ { seg }) \cup LeftSet(seg, p) \cup RightSet(seg, p)
          /\ pc' = "qs1"
          /\ A0' = A0

Next == qs1

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeInv ==
  /\ A \in [1..N -> 1..N]
  /\ S \subseteq Intervals
  /\ pc \in {"qs1", "Done"}

PermInv ==
  IsFullPerm(A, A0)

Inv == TypeInv /\ PermInv

Termination == <> (pc = "Done")
====