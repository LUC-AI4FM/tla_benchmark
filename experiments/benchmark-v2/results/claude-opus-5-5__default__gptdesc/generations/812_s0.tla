---------------------------- MODULE Majority ----------------------------
(***************************************************************************)
(* Boyer and Moore's majority vote algorithm.  The algorithm scans an      *)
(* input sequence of values in one pass, maintaining an index i, a current *)
(* candidate cand and a counter cnt.  When the scan has completed, any     *)
(* value that has an absolute majority in the sequence must equal cand.    *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS A,     \* the set of values
          seq    \* the input sequence of values

ASSUME ConstantAssumption ==
  /\ A # {}
  /\ seq \in Seq(A)

VARIABLES i,     \* next position of the sequence to be examined
          cand,  \* current candidate for having a majority
          cnt    \* lower bound on the number of occurrences of cand

vars == <<i, cand, cnt>>

TypeOK ==
  /\ i \in 1 .. (Len(seq) + 1)
  /\ cand \in A
  /\ cnt \in Nat

Init ==
  /\ i = 1
  /\ cand \in A
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
(* Auxiliary definitions for stating correctness.                          *)
(***************************************************************************)
\* set of positions before j at which v occurs
PositionsBefore(v, j) == { k \in 1 .. (j - 1) : seq[k] = v }

\* number of occurrences of v before position j
OccurrencesBefore(v, j) == Cardinality(PositionsBefore(v, j))

\* number of occurrences of v in the entire sequence
Occurrences(v) == OccurrencesBefore(v, Len(seq) + 1)

(***************************************************************************)
(* Correctness: when the scan is complete, any value having an absolute    *)
(* majority must equal cand.                                               *)
(***************************************************************************)
Correct ==
  i > Len(seq) =>
    \A v \in A : 2 * Occurrences(v) > Len(seq) => v = cand

(***************************************************************************)
(* Inductive invariant used for reasoning about the algorithm.             *)
(***************************************************************************)
Inv ==
  /\ TypeOK
  /\ cnt <= OccurrencesBefore(cand, i)
  /\ 2 * (OccurrencesBefore(cand, i) - cnt) <= i - 1 - cnt
  /\ \A v \in A \ {cand} : 2 * OccurrencesBefore(v, i) <= i - 1 - cnt

(***************************************************************************)
(* Liveness: the scan eventually terminates.                               *)
(***************************************************************************)
Termination == <>(i > Len(seq))

THEOREM Spec => []TypeOK
THEOREM Spec => []Inv
THEOREM Spec => []Correct
THEOREM Spec => Termination
=============================================================================