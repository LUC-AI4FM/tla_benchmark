---------------------------- MODULE MCMajority ----------------------------
(***************************************************************************)
(* Model-checking wrapper for the Boyer-Moore majority vote algorithm      *)
(* over bounded sequences drawn from the three constant elements A, B, C.  *)
(* The algorithm is included inline so that the module is self-contained   *)
(* and passes SANY on its own.                                             *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS A, B, C, bound

ASSUME bound \in Nat

(***************************************************************************)
(* The value set and the bounded-sequence helper.                          *)
(***************************************************************************)
Value == {A, B, C}

BoundedSeq(S) == UNION {[1..n -> S] : n \in 0..bound}

VARIABLES seq, i, cand, cnt

vars == <<seq, i, cand, cnt>>

(***************************************************************************)
(* Auxiliary definitions.                                                  *)
(***************************************************************************)
\* Positions of v in seq strictly before position j
PositionsBefore(v, j) == {k \in 1..(j-1) : seq[k] = v}

\* Number of occurrences of v in seq strictly before position j
OccurrencesBefore(v, j) == Cardinality(PositionsBefore(v, j))

\* Number of occurrences of v in the whole sequence
Occurrences(v) == OccurrencesBefore(v, Len(seq) + 1)

\* v is a strict majority element of seq
IsMajority(v) == 2 * Occurrences(v) > Len(seq)

(***************************************************************************)
(* Initial condition.                                                      *)
(***************************************************************************)
Init ==
    /\ seq \in BoundedSeq(Value)
    /\ i = 1
    /\ cand \in Value
    /\ cnt = 0

(***************************************************************************)
(* Next-state relation.                                                    *)
(***************************************************************************)
Step ==
    /\ i <= Len(seq)
    /\ i' = i + 1
    /\ seq' = seq
    /\ IF cnt = 0
         THEN /\ cand' = seq[i]
              /\ cnt' = 1
         ELSE IF cand = seq[i]
                THEN /\ cnt' = cnt + 1
                     /\ cand' = cand
                ELSE /\ cnt' = cnt - 1
                     /\ cand' = cand

\* Stuttering after termination to avoid reporting deadlock
Terminated ==
    /\ i > Len(seq)
    /\ UNCHANGED vars

Next == Step \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

(***************************************************************************)
(* Safety properties.                                                      *)
(***************************************************************************)
TypeOK ==
    /\ seq \in Seq(Value)
    /\ i \in 1..(Len(seq) + 1)
    /\ cand \in Value
    /\ cnt \in 0..Len(seq)

\* Inductive invariant of the Boyer-Moore algorithm
Inv ==
    /\ cnt <= OccurrencesBefore(cand, i)
    /\ 2 * (OccurrencesBefore(cand, i) - cnt) <= i - 1 - cnt
    /\ \A v \in Value \ {cand} : 2 * OccurrencesBefore(v, i) <= i - 1 - cnt

\* If the algorithm has terminated and a majority element exists,
\* then the candidate is that majority element.
Correctness ==
    (i > Len(seq)) => \A v \in Value : IsMajority(v) => cand = v

(***************************************************************************)
(* Liveness property.                                                      *)
(***************************************************************************)
Termination == <>(i > Len(seq))

=============================================================================