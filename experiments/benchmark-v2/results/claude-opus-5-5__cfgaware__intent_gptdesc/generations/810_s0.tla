---------------------------- MODULE MajorityVote ----------------------------
(***************************************************************************)
(* Boyer-Moore majority-vote algorithm over finite sequences of values     *)
(* drawn from {A, B, C}, with length at most `bound'.  An input sequence   *)
(* is chosen nondeterministically, then the algorithm scans it one element *)
(* per step, maintaining a candidate and a counter.                        *)
(*                                                                         *)
(* Sequences are modelled as functions 1..n -> Value, so the standard      *)
(* Sequences module is not extended.  This avoids a clash with the         *)
(* operator name Seq defined here.                                         *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS A, B, C, bound

ASSUME bound \in Nat

Value == {A, B, C}

\* Distinguished "no candidate" marker, assumed distinct from A, B and C.
NoCand == "none"

\* All finite sequences over S whose length is at most bound.
Seq(S) == UNION { [1..n -> S] : n \in 0..bound }

\* All admissible input sequences, of every length from 0 to bound.
BoundedSeq == Seq(Value)

Len(s) == CHOOSE n \in 0..bound : DOMAIN s = 1..n

\* Number of occurrences of v in s.
Count(s, v) == Cardinality({ k \in DOMAIN s : s[k] = v })

\* v occurs in strictly more than half the positions of s.
IsMajority(s, v) == 2 * Count(s, v) > Len(s)

VARIABLES seq, i, cand, cnt

vars == <<seq, i, cand, cnt>>

-----------------------------------------------------------------------------
Init ==
    /\ seq \in BoundedSeq
    /\ i = 1
    /\ cand = NoCand
    /\ cnt = 0

\* Process element seq[i] according to the majority-vote update rules.
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

Done == i > Len(seq)

\* After termination, the system stutters.  This avoids a reported deadlock.
Terminated ==
    /\ Done
    /\ UNCHANGED vars

Next == Step \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

-----------------------------------------------------------------------------
\* Well-formedness of the state.
TypeOK ==
    /\ seq \in BoundedSeq
    /\ i \in 1..(bound + 1)
    /\ i <= Len(seq) + 1
    /\ cand \in Value \cup {NoCand}
    /\ cnt \in 0..bound
    /\ cnt >= 0
    /\ cnt <= i - 1
    /\ (cand = NoCand) => (cnt = 0)

\* Safety: once the scan is complete, any strict majority is the candidate.
Correct ==
    Done => \A v \in Value : IsMajority(seq, v) => cand = v

\* Prefix-majority invariant.  If v has a strict majority in the processed
\* prefix seq[1..i-1], then v is the candidate.
PrefixCorrect ==
    LET pre == [k \in 1..(i - 1) |-> seq[k]]
    IN  \A v \in Value :
          (2 * Cardinality({ k \in 1..(i - 1) : pre[k] = v }) > i - 1)
              => cand = v

Inv == TypeOK /\ Correct /\ PrefixCorrect

-----------------------------------------------------------------------------
\* Temporal properties.

\* The counter and candidate change only according to the allowed rules.
\* The input sequence never changes.
AllowedUpdates ==
    [][ /\ seq' = seq
        /\ \/ /\ cnt = 0
              /\ cand' \in Value
              /\ cnt' = 1
           \/ /\ cnt > 0
              /\ cand' = cand
              /\ cnt' \in {cnt + 1, cnt - 1}
      ]_<<seq, cand, cnt>>

CounterNonNegative == [](cnt >= 0)

AlwaysCorrect == []Correct

Termination == <>Done

=============================================================================