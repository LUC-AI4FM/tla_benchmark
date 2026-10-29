---------------------------- MODULE MajorityVote ----------------------------
(***************************************************************************)
(* Boyer-Moore majority vote algorithm.                                    *)
(* The input sequence is chosen nondeterministically among all sequences  *)
(* over Value of length at most BOUND. The algorithm processes it in one  *)
(* pass, keeping only a candidate and a counter. At termination, any value *)
(* with an absolute majority must be the candidate.                        *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Value, BOUND

ASSUME ConstantsOK == Value # {} /\ BOUND \in Nat

\* All sequences over S of length at most n
BoundedSeq(S, n) == UNION { [1..k -> S] : k \in 0..n }

VARIABLES seq,   \* input sequence
          i,     \* index of next element to examine
          cand,  \* current candidate
          cnt    \* current counter

vars == <<seq, i, cand, cnt>>

\* Number of occurrences of v among the first j elements of seq
OccurrencesUpTo(v, j) == Cardinality({ k \in 1..j : seq[k] = v })

\* Number of occurrences of v in the whole sequence
Occurrences(v) == OccurrencesUpTo(v, Len(seq))

TypeOK ==
  /\ seq \in BoundedSeq(Value, BOUND)
  /\ i \in 1..(Len(seq) + 1)
  /\ cand \in Value
  /\ cnt \in Nat

Init ==
  /\ seq \in BoundedSeq(Value, BOUND)
  /\ i = 1
  /\ cand \in Value
  /\ cnt = 0

Step ==
  /\ i <= Len(seq)
  /\ IF cnt = 0
       THEN /\ cand' = seq[i]
            /\ cnt' = 1
       ELSE /\ cand' = cand
            /\ cnt' = IF cand = seq[i] THEN cnt + 1 ELSE cnt - 1
  /\ i' = i + 1
  /\ UNCHANGED seq

Done == i > Len(seq)

\* Allow stuttering after termination (avoid deadlock reports)
Terminated ==
  /\ Done
  /\ UNCHANGED vars

Next == Step \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

-----------------------------------------------------------------------------
(* Safety properties *)

\* Main correctness: upon termination, any majority value is the candidate.
Correctness ==
  Done => \A v \in Value : (2 * Occurrences(v) > Len(seq)) => v = cand

\* Equivalent formulation: any non-candidate is not a majority on termination.
NonCandidateNotMajority ==
  Done => \A v \in Value \ {cand} : 2 * Occurrences(v) <= Len(seq)

\* Inductive invariant implying Correctness
Inv ==
  /\ TypeOK
  /\ cnt <= OccurrencesUpTo(cand, i - 1)
  /\ \A v \in Value \ {cand} :
        2 * OccurrencesUpTo(v, i - 1) <= (i - 1) - cnt

(* Liveness: the algorithm terminates after processing all elements *)
Termination == <>Done

THEOREM Spec => [](Inv /\ Correctness /\ NonCandidateNotMajority)
THEOREM Spec => Termination
=============================================================================