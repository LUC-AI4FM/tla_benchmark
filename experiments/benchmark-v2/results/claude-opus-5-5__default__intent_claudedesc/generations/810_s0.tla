---------------------------- MODULE MajorityVote ----------------------------
(***************************************************************************)
(* Boyer-Moore majority vote algorithm.                                    *)
(* The input sequence is chosen nondeterministically among all sequences   *)
(* over Value of length at most MaxLen, so model checking covers every     *)
(* input within the bounds.                                                *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Value,    \* finite set of possible elements (e.g. {a, b, c})
          MaxLen    \* bound on the length of the input sequence

ASSUME /\ Value # {}
       /\ IsFiniteSet(Value)
       /\ MaxLen \in Nat

VARIABLES seq,   \* the input sequence
          i,     \* index of the next element to process
          cand,  \* current candidate
          cnt    \* counter

vars == <<seq, i, cand, cnt>>

\* All sequences over Value of length at most MaxLen
BoundedSeq == UNION { [1..n -> Value] : n \in 0..MaxLen }

\* Number of occurrences of v in seq[1..k-1]
OccurrencesBefore(v, k) == Cardinality({ j \in 1..(k-1) : seq[j] = v })

\* Number of occurrences of v in the whole sequence
Occurrences(v) == OccurrencesBefore(v, Len(seq) + 1)

\* v is a majority element: it appears more than floor(n/2) times
IsMajority(v) == 2 * Occurrences(v) > Len(seq)

Done == i > Len(seq)

-----------------------------------------------------------------------------
Init ==
  /\ seq \in BoundedSeq
  /\ i = 1
  /\ cand \in Value
  /\ cnt = 0

Step ==
  /\ i <= Len(seq)
  /\ IF cnt = 0
       THEN /\ cand' = seq[i]
            /\ cnt' = 1
       ELSE IF cand = seq[i]
              THEN /\ cnt' = cnt + 1
                   /\ UNCHANGED cand
              ELSE /\ cnt' = cnt - 1
                   /\ UNCHANGED cand
  /\ i' = i + 1
  /\ UNCHANGED seq

\* Allow stuttering after termination to avoid deadlock
Terminated ==
  /\ Done
  /\ UNCHANGED vars

Next == Step \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
TypeOK ==
  /\ seq \in BoundedSeq
  /\ i \in 1..(Len(seq) + 1)
  /\ cand \in Value
  /\ cnt \in 0..Len(seq)

\* Inductive invariant: no element (in particular a true majority element)
\* can have been canceled out by the counting mechanism.
Inv ==
  /\ i <= Len(seq) + 1
  /\ cnt <= OccurrencesBefore(cand, i)
  /\ 2 * (OccurrencesBefore(cand, i) - cnt) <= i - 1 - cnt
  /\ \A v \in Value \ {cand} : 2 * OccurrencesBefore(v, i) <= i - 1 - cnt

\* Majority element can never be canceled out
MajorityNotCanceled ==
  \A v \in Value :
     IsMajority(v) =>
        \/ v = cand
        \/ 2 * OccurrencesBefore(v, i) <= i - 1 - cnt

\* Partial correctness: upon termination, the candidate is the majority
\* element whenever one exists.
Correctness ==
  Done => \A v \in Value : IsMajority(v) => cand = v

\* Termination: the algorithm eventually finishes processing the input
Termination == <>Done

THEOREM Spec => [](TypeOK /\ Inv /\ MajorityNotCanceled /\ Correctness)
THEOREM Spec => Termination
=============================================================================