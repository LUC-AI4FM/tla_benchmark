------------------------------ MODULE MCMajority ------------------------------
(***************************************************************************)
(* Model-checking wrapper for a majority-vote (Boyer-Moore) setting over   *)
(* bounded sequences drawn from three constant elements A, B and C.        *)
(* The description leaves the algorithm to an external Majority module.   *)
(* So that this module is self-contained and parses with SANY, the         *)
(* standard Boyer-Moore majority vote algorithm is written out here over   *)
(* the variables seq, i, cand and cnt.                                     *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS A, B, C, Bound

ASSUME Bound \in Nat

\* The set of values
Value == {A, B, C}

\* All sequences over S with lengths from 0 to Bound
BoundedSeq(S) == UNION { [1..n -> S] : n \in 0..Bound }

VARIABLES seq, i, cand, cnt

vars == <<seq, i, cand, cnt>>

-----------------------------------------------------------------------------
(* Helper operators *)

\* Positions in seq before index j that hold value v
PositionsBefore(v, j) == { k \in 1..(j-1) : seq[k] = v }

\* Number of occurrences of v in seq before index j
OccurrencesBefore(v, j) == Cardinality(PositionsBefore(v, j))

\* Number of occurrences of v in the whole sequence
Occurrences(v) == OccurrencesBefore(v, Len(seq) + 1)

-----------------------------------------------------------------------------
(* Algorithm *)

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

\* Stuttering after the algorithm has scanned the whole sequence
Done ==
    /\ i > Len(seq)
    /\ UNCHANGED vars

Next == Step \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

-----------------------------------------------------------------------------
(* Properties *)

TypeOK ==
    /\ seq \in Seq(Value)
    /\ i \in 1..(Len(seq) + 1)
    /\ cand \in Value
    /\ cnt \in 0..Len(seq)

\* If a value occurs in a strict majority of positions, then once the
\* algorithm terminates the candidate is that value.
Correctness ==
    (i > Len(seq)) =>
        \A v \in Value : 2 * Occurrences(v) > Len(seq) => cand = v

\* Inductive invariant implying Correctness
Inv ==
    /\ i \in 1..(Len(seq) + 1)
    /\ cnt <= OccurrencesBefore(cand, i)
    /\ 2 * (OccurrencesBefore(cand, i) - cnt) <= i - 1 - cnt
    /\ \A v \in Value \ {cand} : 2 * OccurrencesBefore(v, i) <= i - 1 - cnt

\* The algorithm eventually scans the whole sequence
Termination == <>(i > Len(seq))

=============================================================================