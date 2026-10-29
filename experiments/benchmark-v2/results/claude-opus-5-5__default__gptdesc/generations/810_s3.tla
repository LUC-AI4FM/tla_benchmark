---------------------------- MODULE MCMajority ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS A, B, C, bound

ASSUME bound \in Nat

Value == {A, B, C}

BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

vars == <<seq, i, cand, cnt>>

-----------------------------------------------------------------------------
(* Number of occurrences of v in seq strictly before position j *)
OccurrencesBefore(v, j) == Cardinality({k \in 1 .. (j - 1) : seq[k] = v})

Occurrences(v) == OccurrencesBefore(v, Len(seq) + 1)

TypeOK ==
    /\ seq \in BoundedSeq(Value)
    /\ i \in 1 .. (Len(seq) + 1)
    /\ cand \in Value
    /\ cnt \in 0 .. Len(seq)

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

Done ==
    /\ i > Len(seq)
    /\ UNCHANGED vars

Next == Step \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

-----------------------------------------------------------------------------
(* Safety: count never exceeds occurrences of the candidate seen so far *)
CountBound ==
    cnt <= OccurrencesBefore(cand, i)

(* Safety: if some value has a strict majority, the final candidate is it *)
Correctness ==
    i > Len(seq) =>
        \A v \in Value : 2 * Occurrences(v) > Len(seq) => v = cand

(* Liveness: the algorithm eventually scans the whole sequence *)
Termination == <>(i > Len(seq))

=============================================================================