------------------------------ MODULE MCMajority ------------------------------
(***************************************************************************)
(* Model-checking harness for the Boyer-Moore majority vote algorithm.     *)
(* The algorithm from the Majority module is restated here so that this    *)
(* module stands alone. The unbounded Seq(Value) is replaced by            *)
(* BoundedSeq(Value), which allows only finite sequences of length         *)
(* 0..BOUND. This makes the state space finite for TLC.                    *)
(* TLC configuration: INVARIANTS TypeOK Correct Inv; CHECK_DEADLOCK FALSE  *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C,   \* model values
          BOUND      \* maximum length of the input sequence

ASSUME BOUND \in Nat

VARIABLES seq,   \* input sequence
          i,     \* next position to be processed
          cand,  \* current majority candidate
          cnt    \* counter for the candidate

vars == <<seq, i, cand, cnt>>

Value == {A, B, C}

(* Finite replacement for Seq(S): all sequences over S of length <= BOUND *)
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. BOUND }

-----------------------------------------------------------------------------
(* Majority vote algorithm (as in the Majority module) *)

Init ==
    /\ seq \in BoundedSeq(Value)
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

-----------------------------------------------------------------------------
(* Properties *)

TypeOK ==
    /\ seq \in BoundedSeq(Value)
    /\ i \in 1 .. Len(seq) + 1
    /\ cand \in Value
    /\ cnt \in Nat

\* positions of v in seq strictly before position i
PositionsBefore(v, j) == { k \in 1 .. (j - 1) : seq[k] = v }

\* number of occurrences of v in the whole sequence
OccurrencesOf(v) == Cardinality(PositionsBefore(v, Len(seq) + 1))

\* Correctness: once the whole sequence is processed, any majority
\* element equals the candidate.
Correct ==
    i > Len(seq) =>
        \A v \in Value : 2 * OccurrencesOf(v) > Len(seq) => v = cand

\* Inductive invariant supporting correctness
Inv ==
    /\ cnt <= Cardinality(PositionsBefore(cand, i))
    /\ 2 * (Cardinality(PositionsBefore(cand, i)) - cnt) <= i - 1 - cnt
    /\ \A v \in Value \ {cand} :
          2 * Cardinality(PositionsBefore(v, i)) <= i - 1 - cnt

\* Liveness: the algorithm eventually finishes processing the sequence
Termination == <>(i > Len(seq))

=============================================================================