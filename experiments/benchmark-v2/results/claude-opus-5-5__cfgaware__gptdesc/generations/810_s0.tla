---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets

CONSTANTS A, B, C, bound

Value == {A, B, C}

Seq(S) == UNION { [1..n -> S] : n \in 0..bound }

BoundedSeq(S) == UNION { [1..n -> S] : n \in 0..bound }

Len(s) == CHOOSE n \in 0..bound : DOMAIN s = 1..n

VARIABLES seq, i, cand, cnt

vars == <<seq, i, cand, cnt>>

PositionsBefore(v, j) == { k \in 1..(j-1) : seq[k] = v }

OccurrencesBefore(v, j) == Cardinality(PositionsBefore(v, j))

Occurrences(v) == OccurrencesBefore(v, Len(seq) + 1)

Init ==
    /\ seq \in BoundedSeq(Value)
    /\ i = 1
    /\ cand \in Value
    /\ cnt = 0

Next ==
    /\ i <= Len(seq)
    /\ i' = i + 1
    /\ seq' = seq
    /\ IF cnt = 0
          THEN /\ cand' = seq[i]
               /\ cnt' = 1
          ELSE IF cand = seq[i]
                  THEN /\ cand' = cand
                       /\ cnt' = cnt + 1
                  ELSE /\ cand' = cand
                       /\ cnt' = cnt - 1

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ seq \in BoundedSeq(Value)
    /\ i \in 1..(Len(seq) + 1)
    /\ cand \in Value
    /\ cnt \in Nat

Correct ==
    i > Len(seq) =>
        \A v \in Value : 2 * Occurrences(v) > Len(seq) => cand = v

Inv ==
    /\ TypeOK
    /\ cnt <= OccurrencesBefore(cand, i)
    /\ 2 * (OccurrencesBefore(cand, i) - cnt) <= i - 1 - cnt
    /\ \A v \in Value \ {cand} : 2 * OccurrencesBefore(v, i) <= i - 1 - cnt

====