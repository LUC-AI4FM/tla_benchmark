------------------------------- MODULE MCMajority -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

ASSUME bound \in Nat

Value == {A, B, C}

BoundedSeq(S) == UNION { [1..n -> S] : n \in 0..bound }

VARIABLES seq, i, cand, cnt

vars == <<seq, i, cand, cnt>>

(* Number of occurrences of value v in the first j positions of seq *)
OccurrencesUpTo(v, j) == Cardinality({ k \in 1..j : seq[k] = v })

Occurrences(v) == OccurrencesUpTo(v, Len(seq))

TypeOK ==
    /\ seq \in BoundedSeq(Value)
    /\ i \in 1..(Len(seq) + 1)
    /\ cand \in Value
    /\ cnt \in 0..Len(seq)

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
                  THEN /\ cnt' = cnt + 1
                       /\ UNCHANGED cand
                  ELSE /\ cnt' = cnt - 1
                       /\ UNCHANGED cand

Done ==
    /\ i > Len(seq)
    /\ UNCHANGED vars

Next == Step \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

(* Safety: if some value occurs in a strict majority of positions,
   the algorithm's candidate at termination is that value. *)
Correctness ==
    (i > Len(seq)) =>
        \A v \in Value : (2 * Occurrences(v) > Len(seq)) => cand = v

(* Auxiliary invariant relating the counter to the prefix processed so far *)
CountBound ==
    /\ cnt <= i - 1
    /\ (cnt > 0) => (2 * OccurrencesUpTo(cand, i - 1) >= cnt + 0)

(* Liveness: the algorithm eventually finishes scanning the sequence *)
Termination == <>(i > Len(seq))

THEOREM Spec => [](TypeOK /\ Correctness /\ CountBound)
THEOREM Spec => Termination
=================================================================================