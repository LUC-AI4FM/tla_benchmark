---------------------------- MODULE MajorityVote ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS A, B, C, bound

ASSUME bound \in Nat

Value == {A, B, C}

\* Finite sequences over S (overridable in the model by BoundedSeq)
Seq(S) == UNION { [1..n -> S] : n \in Nat }

\* Sequences over S of length at most bound
BoundedSeq(S) == UNION { [1..n -> S] : n \in 0..bound }

Len(s) == Cardinality(DOMAIN s)

VARIABLES seq, i, cand, cnt

vars == <<seq, i, cand, cnt>>

\* Number of occurrences of v among the first k elements of s
Occ(v, s, k) == Cardinality({ j \in 1..k : s[j] = v })

Init ==
    /\ seq \in BoundedSeq(Value)
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

Terminated ==
    /\ i > Len(seq)
    /\ UNCHANGED vars

Next == Step \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

-----------------------------------------------------------------------------

TypeOK ==
    /\ seq \in BoundedSeq(Value)
    /\ i \in 1..(Len(seq) + 1)
    /\ cand \in Value
    /\ cnt \in 0..(i - 1)

\* Partial correctness: on termination, any majority element is the candidate
Correct ==
    i > Len(seq) =>
        \A v \in Value :
            2 * Occ(v, seq, Len(seq)) > Len(seq) => cand = v

\* Inductive invariant: the majority element cannot have been canceled out
Inv ==
    /\ TypeOK
    /\ cnt <= Occ(cand, seq, i - 1)
    /\ 2 * (Occ(cand, seq, i - 1) - cnt) <= (i - 1) - cnt
    /\ \A v \in Value \ {cand} :
           2 * Occ(v, seq, i - 1) <= (i - 1) - cnt

\* Termination: the algorithm eventually processes the whole sequence
Termination == <>(i > Len(seq))

=============================================================================