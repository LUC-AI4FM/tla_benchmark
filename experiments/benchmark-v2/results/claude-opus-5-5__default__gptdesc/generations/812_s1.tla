---- MODULE Majority ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANT Value
ASSUME ConstAssump == Value # {}

CONSTANT seq
ASSUME SeqAssump == seq \in Seq(Value)

VARIABLES i, cand, cnt
vars == <<i, cand, cnt>>

TypeOK ==
  /\ i \in 1 .. Len(seq) + 1
  /\ cand \in Value
  /\ cnt \in Nat

Init ==
  /\ i = 1
  /\ cand \in Value
  /\ cnt = 0

Next ==
  /\ i <= Len(seq)
  /\ i' = i + 1
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

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Auxiliary definitions for reasoning about the algorithm
PositionsBefore(v, j) == { k \in 1 .. (j - 1) : seq[k] = v }

OccurrencesBefore(v, j) == Cardinality(PositionsBefore(v, j))

Occurrences(v) == OccurrencesBefore(v, Len(seq) + 1)

\* Correctness: if the scan is complete, any value with an absolute majority equals cand
Correctness ==
  i > Len(seq) =>
    \A v \in Value : 2 * Occurrences(v) > Len(seq) => v = cand

\* Inductive invariant used for reasoning about the algorithm
Inv ==
  /\ TypeOK
  /\ i <= Len(seq) + 1
  /\ cnt <= OccurrencesBefore(cand, i)
  /\ 2 * (OccurrencesBefore(cand, i) - cnt) <= i - 1 - cnt
  /\ \A v \in Value \ {cand} :
        2 * OccurrencesBefore(v, i) <= i - 1 - cnt

\* Liveness: the scan eventually completes
Termination == <>(i > Len(seq))

THEOREM Spec => []Correctness
THEOREM Spec => []Inv
THEOREM Spec => Termination
====