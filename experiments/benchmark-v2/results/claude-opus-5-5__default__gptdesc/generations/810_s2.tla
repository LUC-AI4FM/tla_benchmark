---------------------------- MODULE MCMajority ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

ASSUME /\ A # B /\ B # C /\ A # C
       /\ bound \in Nat

Value == {A, B, C}

BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

vars == <<seq, i, cand, cnt>>

-----------------------------------------------------------------------------
(* Helper operators                                                        *)
-----------------------------------------------------------------------------

PositionsBefore(v, j) == { k \in 1 .. (j - 1) : seq[k] = v }

OccurrencesBefore(v, j) == Cardinality(PositionsBefore(v, j))

Occurrences(v) == OccurrencesBefore(v, Len(seq) + 1)

-----------------------------------------------------------------------------
(* Initial condition and transitions (Boyer-Moore majority vote)           *)
-----------------------------------------------------------------------------

Init ==
    /\ seq \in BoundedSeq(Value)
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

Terminating ==
    /\ i > Len(seq)
    /\ UNCHANGED vars

Next == Step \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

-----------------------------------------------------------------------------
(* Properties                                                              *)
-----------------------------------------------------------------------------

TypeOK ==
    /\ seq \in BoundedSeq(Value)
    /\ i \in 1 .. (Len(seq) + 1)
    /\ cand \in Value
    /\ cnt \in 0 .. (i - 1)

Correctness ==
    i > Len(seq) =>
        \A v \in Value : 2 * Occurrences(v) > Len(seq) => v = cand

Inv ==
    /\ cnt <= OccurrencesBefore(cand, i)
    /\ 2 * (OccurrencesBefore(cand, i) - cnt) <= i - 1 - cnt
    /\ \A v \in Value \ {cand} : 2 * OccurrencesBefore(v, i) <= i - 1 - cnt

Termination == <>(i > Len(seq))

=============================================================================