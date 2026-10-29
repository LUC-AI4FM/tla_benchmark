---------------------------- MODULE MajorityVote ----------------------------
(***************************************************************************)
(* Boyer-Moore majority vote algorithm.                                    *)
(* The algorithm scans the input sequence seq once, maintaining a          *)
(* candidate value and a counter. Upon termination, any value that        *)
(* occurs in more than half of the positions of seq is the candidate.     *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANT Value
ASSUME ValueNonEmpty == Value # {}

CONSTANT seq
ASSUME SeqAssumption == seq \in Seq(Value)

VARIABLES i, cand, cnt

vars == <<i, cand, cnt>>

(***************************************************************************)
(* Auxiliary definitions                                                   *)
(***************************************************************************)
\* Positions of the sequence strictly before index j that hold value v.
PositionsBefore(v, j) == {k \in 1..(j-1) : seq[k] = v}

\* Number of occurrences of v strictly before position j.
OccurrencesBefore(v, j) == Cardinality(PositionsBefore(v, j))

\* Number of occurrences of v in the entire sequence.
Occurrences(v) == OccurrencesBefore(v, Len(seq) + 1)

\* Value v has an absolute majority in seq.
IsMajority(v) == 2 * Occurrences(v) > Len(seq)

(***************************************************************************)
(* Algorithm                                                               *)
(***************************************************************************)
Init ==
    /\ i = 1
    /\ cand \in Value
    /\ cnt = 0

Step ==
    /\ i <= Len(seq)
    /\ i' = i + 1
    /\ IF cnt = 0
          THEN /\ cand' = seq[i]
               /\ cnt' = 1
          ELSE IF cand = seq[i]
                  THEN /\ cnt' = cnt + 1
                       /\ UNCHANGED cand
                  ELSE /\ cnt' = cnt - 1
                       /\ UNCHANGED cand

Done ==
    /\ i > Len(seq)
    /\ UNCHANGED vars

Next == Step \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
TypeOK ==
    /\ i \in 1..(Len(seq) + 1)
    /\ cand \in Value
    /\ cnt \in 0..Len(seq)

\* Upon termination, every non-candidate value is not a majority.
Correct ==
    i > Len(seq) =>
        \A v \in Value : IsMajority(v) => v = cand

\* Inductive invariant implying Correct.
Inv ==
    /\ TypeOK
    /\ cnt <= i - 1
    /\ 2 * (OccurrencesBefore(cand, i) - cnt) <= i - 1 - cnt
    /\ \A v \in Value \ {cand} :
           2 * OccurrencesBefore(v, i) <= i - 1 - cnt

\* The algorithm eventually terminates.
Termination == <>(i > Len(seq))

=============================================================================