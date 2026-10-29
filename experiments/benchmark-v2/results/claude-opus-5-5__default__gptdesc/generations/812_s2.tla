------------------------------ MODULE Majority ------------------------------
(***************************************************************************)
(* Boyer and Moore's majority vote algorithm. The algorithm scans an      *)
(* input sequence in a single pass, maintaining an index i, a current     *)
(* candidate cand and a counter cnt. When the scan is complete, any       *)
(* value that has an absolute majority in the sequence equals cand.       *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Value,   \* the set of possible values
          seq      \* the input sequence

ASSUME ValueAssump == Value # {}
ASSUME SeqAssump   == seq \in Seq(Value)

VARIABLES i,     \* index of the next element of seq to read
          cand,  \* current candidate for the majority value
          cnt    \* counter associated with the candidate

vars == <<i, cand, cnt>>

TypeOK ==
    /\ i \in 1 .. (Len(seq) + 1)
    /\ cand \in Value
    /\ cnt \in 0 .. Len(seq)

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

(***************************************************************************)
(* Auxiliary definitions for stating correctness.                         *)
(***************************************************************************)
\* set of positions strictly before j that hold value v
PositionsBefore(v, j) == { k \in 1 .. (j - 1) : seq[k] = v }

\* number of occurrences of v strictly before position j
OccurrencesBefore(v, j) == Cardinality(PositionsBefore(v, j))

\* total number of occurrences of v in the whole sequence
Occurrences(v) == OccurrencesBefore(v, Len(seq) + 1)

(***************************************************************************)
(* Correctness: when the scan is complete, any value with an absolute     *)
(* majority equals the candidate.                                         *)
(***************************************************************************)
Correct ==
    i > Len(seq) =>
        \A v \in Value : 2 * Occurrences(v) > Len(seq) => v = cand

(***************************************************************************)
(* Inductive invariant used for reasoning about the algorithm.            *)
(***************************************************************************)
Inv ==
    /\ TypeOK
    /\ cnt <= OccurrencesBefore(cand, i)
    /\ 2 * (OccurrencesBefore(cand, i) - cnt) <= i - 1 - cnt
    /\ \A v \in Value \ {cand} : 2 * OccurrencesBefore(v, i) <= i - 1 - cnt

(***************************************************************************)
(* Liveness: the scan eventually completes.                               *)
(***************************************************************************)
Termination == <>(i > Len(seq))

THEOREM Spec => []TypeOK
THEOREM Spec => []Inv
THEOREM Spec => []Correct
THEOREM Spec => Termination
=============================================================================