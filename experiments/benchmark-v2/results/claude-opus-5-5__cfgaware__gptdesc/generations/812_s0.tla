------------------------------ MODULE Majority ------------------------------
(***************************************************************************)
(* Boyer and Moore's majority vote algorithm. A single pass over the input *)
(* sequence maintains a candidate and a counter. When the scan completes,  *)
(* any value that holds an absolute majority in the sequence equals cand.  *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Value, seq

ASSUME ConstAssump ==
  /\ Value # {}
  /\ seq \in Seq(Value)

VARIABLES i, cand, cnt

vars == <<i, cand, cnt>>

TypeOK ==
  /\ i \in 1 .. Len(seq) + 1
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
(* Auxiliary definitions for stating correctness and the invariant.        *)
(***************************************************************************)
\* positions in the prefix seq[1..j-1] that hold value v
PositionsBefore(v, j) == {k \in 1 .. (j - 1) : seq[k] = v}

\* all positions in seq that hold value v
Positions(v) == PositionsBefore(v, Len(seq) + 1)

\* correctness: once the scan is complete, any majority value equals cand
Correct ==
  i > Len(seq) =>
    \A v \in Value :
      2 * Cardinality(Positions(v)) > Len(seq) => v = cand

\* inductive invariant used to prove correctness
Inv ==
  /\ cnt <= Cardinality(PositionsBefore(cand, i))
  /\ 2 * (Cardinality(PositionsBefore(cand, i)) - cnt) <= i - 1 - cnt
  /\ \A v \in Value \ {cand} :
        2 * Cardinality(PositionsBefore(v, i)) <= i - 1 - cnt

=============================================================================