------------------------------ MODULE Majority ------------------------------
(***************************************************************************)
(* Boyer and Moore's majority vote algorithm. The algorithm scans an input *)
(* sequence of values in one pass, maintaining an index i, a current       *)
(* candidate cand, and a counter cnt. When the scan is complete, any value *)
(* that has an absolute majority in the sequence must equal cand.          *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANT Value

ASSUME ValueAssumption == Value # {}

VARIABLES seq, i, cand, cnt

vars == <<seq, i, cand, cnt>>

TypeOK ==
  /\ seq \in Seq(Value)
  /\ i \in 1 .. Len(seq) + 1
  /\ cand \in Value
  /\ cnt \in Nat

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

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Auxiliary definitions for stating correctness.                          *)
(***************************************************************************)
PositionsBefore(v, j) == { k \in 1 .. (j - 1) : seq[k] = v }

OccurrencesBefore(v, j) == Cardinality(PositionsBefore(v, j))

Occurrences(v) == OccurrencesBefore(v, Len(seq) + 1)

(***************************************************************************)
(* Correctness: when the scan is complete, any value with an absolute      *)
(* majority equals cand.                                                   *)
(***************************************************************************)
Correctness ==
  i > Len(seq) =>
    \A v \in Value : 2 * Occurrences(v) > Len(seq) => v = cand

(***************************************************************************)
(* Inductive invariant used for reasoning about the algorithm.             *)
(***************************************************************************)
Inv ==
  /\ TypeOK
  /\ cnt <= OccurrencesBefore(cand, i)
  /\ 2 * (OccurrencesBefore(cand, i) - cnt) <= i - 1 - cnt
  /\ \A v \in Value \ {cand} : 2 * OccurrencesBefore(v, i) <= i - 1 - cnt

(***************************************************************************)
(* Liveness: the scan eventually completes.                                *)
(***************************************************************************)
Termination == <>(i > Len(seq))

THEOREM Spec => []TypeOK
THEOREM Spec => []Inv
THEOREM Spec => []Correctness
THEOREM Spec => Termination
=============================================================================