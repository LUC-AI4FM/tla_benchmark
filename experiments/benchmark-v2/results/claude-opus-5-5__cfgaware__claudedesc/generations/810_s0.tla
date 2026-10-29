---------------------------- MODULE MCMajority ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS A, B, C

CONSTANT bound

ASSUME bound \in Nat

Value == {A, B, C}

BoundedSeq(S) == UNION { [1..n -> S] : n \in 0..bound }

Seq(S) == BoundedSeq(S)

Len(s) == Cardinality(DOMAIN s)

VARIABLES seq, i, cand, cnt

vars == <<seq, i, cand, cnt>>

-----------------------------------------------------------------------------

PositionsBefore(v, j) == { k \in 1..(j-1) : seq[k] = v }

OccurrencesBefore(v, j) == Cardinality(PositionsBefore(v, j))

Occurrences(v) == OccurrencesBefore(v, Len(seq) + 1)

Init ==
  /\ seq \in Seq(Value)
  /\ i = 1
  /\ cand \in Value
  /\ cnt = 0

Next ==
  /\ i <= Len(seq)
  /\ i' = i + 1
  /\ seq' = seq
  /\ \/ /\ cnt = 0
        /\ cand' = seq[i]
        /\ cnt' = 1
     \/ /\ cnt # 0
        /\ cand = seq[i]
        /\ cand' = cand
        /\ cnt' = cnt + 1
     \/ /\ cnt # 0
        /\ cand # seq[i]
        /\ cand' = cand
        /\ cnt' = cnt - 1

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

TypeOK ==
  /\ seq \in Seq(Value)
  /\ i \in 1..(Len(seq) + 1)
  /\ cand \in Value
  /\ cnt \in 0..Len(seq)

Correct ==
  i > Len(seq) =>
    \A v \in Value : 2 * Occurrences(v) > Len(seq) => v = cand

Inv ==
  /\ cnt <= OccurrencesBefore(cand, i)
  /\ 2 * (OccurrencesBefore(cand, i) - cnt) <= i - 1 - cnt
  /\ \A v \in Value \ {cand} : 2 * OccurrencesBefore(v, i) <= i - 1 - cnt

=============================================================================