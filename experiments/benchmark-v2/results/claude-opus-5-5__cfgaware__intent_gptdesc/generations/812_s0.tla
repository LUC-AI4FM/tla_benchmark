---------------------------- MODULE Majority ----------------------------
(***************************************************************************)
(* Boyer-Moore majority vote algorithm.                                    *)
(* The input sequence `seq' is chosen nondeterministically, once, among    *)
(* all sequences over Value of length at most MaxLen. It is never changed. *)
(* The algorithm makes one left-to-right pass. Besides the input, it keeps *)
(* only constant extra state: the index i, the candidate cand and the      *)
(* counter cnt. Occurrence counts are used only by the invariants and the  *)
(* correctness property. They are not part of the algorithm's state.       *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Value
ASSUME Value # {}

\* Bound on input length for model checking
MaxLen == 4

BoundedSeq(S, n) == UNION { [1..k -> S] : k \in 0..n }

VARIABLES seq,   \* the input sequence (fixed after initialization)
          i,     \* index of the next element to inspect
          cand,  \* current majority candidate
          cnt    \* current counter of the candidate

vars == <<seq, i, cand, cnt>>

(* Proof-only helpers: occurrences of v among the first j elements *)
PositionsBefore(v, j) == { k \in 1..j : seq[k] = v }
OccBefore(v, j) == Cardinality(PositionsBefore(v, j))
Occ(v) == OccBefore(v, Len(seq))

TypeOK ==
  /\ seq \in BoundedSeq(Value, MaxLen)
  /\ i \in 1..(Len(seq) + 1)
  /\ cand \in Value
  /\ cnt \in 0..(i - 1)

Init ==
  /\ seq \in BoundedSeq(Value, MaxLen)
  /\ i = 1
  /\ cand \in Value
  /\ cnt = 0

Step ==
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

Done ==
  /\ i > Len(seq)
  /\ UNCHANGED vars

Next == Step \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

Terminated == i > Len(seq)

(* Expected output at termination: cand.
   If a strict majority value exists, then cand equals it. *)
Correct ==
  Terminated =>
    \A v \in Value : 2 * Occ(v) > Len(seq) => v = cand

(* Inductive invariant that supports the proof of Correct *)
Inv ==
  /\ TypeOK
  /\ i <= Len(seq) + 1
  /\ cnt <= OccBefore(cand, i - 1)
  /\ 2 * (OccBefore(cand, i - 1) - cnt) <= (i - 1) - cnt
  /\ \A v \in Value \ {cand} : 2 * OccBefore(v, i - 1) <= (i - 1) - cnt

(* Uniqueness of a possible majority *)
MajorityUnique ==
  \A v, w \in Value :
    (2 * Occ(v) > Len(seq) /\ 2 * Occ(w) > Len(seq)) => v = w

(* Liveness: the procedure finishes processing all input elements *)
Termination == <>Terminated

THEOREM Spec => []Inv
THEOREM Spec => []Correct
THEOREM Spec => Termination
==========================================================================