------------------------------ MODULE BoyerMooreMajority ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Value,    \* the fixed, nonempty domain of input values
          MaxLen    \* bound on input length, used only for finite model checking

ASSUME ValueNonempty == Value # {}
ASSUME MaxLenNat     == MaxLen \in Nat

\* All input sequences of length at most MaxLen over Value.
\* Model checking from this set checks every sequence up to the bound.
BoundedSeqs == UNION { [1..n -> Value] : n \in 0..MaxLen }

VARIABLES
    seq,    \* the fixed input sequence, chosen once in Init and never changed
    i,      \* index of the next element to inspect (1-based)
    cand,   \* current majority candidate (constant-size state)
    cnt,    \* current counter (constant-size state)
    pc      \* control state: "loop" or "done"

vars == << seq, i, cand, cnt, pc >>

-----------------------------------------------------------------------------
(* Proof-support definitions.                                               *)
(* These are definitions over the input, not stored program state, so the  *)
(* procedure uses no storage proportional to the input length.              *)
-----------------------------------------------------------------------------

\* Number of occurrences of v among positions 1..k of seq
Count(v, k) == Cardinality({ j \in 1..k : seq[j] = v })

\* Occurrences of v in the whole input
Occurrences(v) == Count(v, Len(seq))

\* v is a strict majority of the whole input
IsMajority(v) == 2 * Occurrences(v) > Len(seq)

\* Number of elements processed so far
Processed == i - 1

-----------------------------------------------------------------------------

Init ==
    /\ seq  \in BoundedSeqs
    /\ i    = 1
    /\ cand \in Value          \* arbitrary initial candidate
    /\ cnt  = 0
    /\ pc   = "loop"

\* Inspect element seq[i] exactly once, in left-to-right order
Step ==
    /\ pc = "loop"
    /\ i <= Len(seq)
    /\ IF cnt = 0
          THEN /\ cand' = seq[i]
               /\ cnt'  = 1
          ELSE IF cand = seq[i]
                  THEN /\ cnt'  = cnt + 1
                       /\ UNCHANGED cand
                  ELSE /\ cnt'  = cnt - 1
                       /\ UNCHANGED cand
    /\ i' = i + 1
    /\ UNCHANGED << seq, pc >>

\* All input processed: report cand
Finish ==
    /\ pc = "loop"
    /\ i > Len(seq)
    /\ pc' = "done"
    /\ UNCHANGED << seq, i, cand, cnt >>

\* After termination the system only stutters
Terminated ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == Step \/ Finish \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Step \/ Finish)

-----------------------------------------------------------------------------
(* Safety properties                                                        *)
-----------------------------------------------------------------------------

TypeOK ==
    /\ seq  \in BoundedSeqs
    /\ i    \in 1..(Len(seq) + 1)
    /\ cand \in Value
    /\ cnt  \in 0..Len(seq)
    /\ pc   \in {"loop", "done"}

\* Inductive invariant supporting the correctness proof
Inv ==
    /\ TypeOK
    /\ cnt <= Processed
    /\ pc = "done" => i = Len(seq) + 1
    \* The counter never exceeds the candidate's occurrences in the processed prefix
    /\ cnt > 0 => cnt <= Count(cand, Processed)
    \* Unmatched occurrences of cand are at most half of the "cancelled" prefix
    /\ 2 * (Count(cand, Processed) - cnt) <= Processed - cnt
    \* Any non-candidate occurs at most half of the "cancelled" prefix
    /\ \A v \in Value \ {cand} : 2 * Count(v, Processed) <= Processed - cnt

\* At most one value can be a strict majority
MajorityUnique ==
    \A v, w \in Value : (IsMajority(v) /\ IsMajority(w)) => v = w

\* Main correctness requirement: at termination, if a strict majority exists,
\* the reported element equals it. No requirement otherwise.
Correctness ==
    pc = "done" => \A v \in Value : IsMajority(v) => cand = v

\* Equivalent formulation: the output is the only possible majority
OutputIsOnlyPossibleMajority ==
    pc = "done" => \A v \in Value : v # cand => ~IsMajority(v)

-----------------------------------------------------------------------------
(* Liveness properties                                                      *)
-----------------------------------------------------------------------------

\* The procedure completes after processing all input elements
Termination == <>(pc = "done")

AllProcessedAtEnd == <>(pc = "done" /\ i = Len(seq) + 1)

\* Once done, it stays done with a stable output
StableOutput == [][pc = "done" => (pc' = "done" /\ cand' = cand)]_vars

-----------------------------------------------------------------------------

THEOREM Spec => []Inv
THEOREM Spec => []MajorityUnique
THEOREM Spec => []Correctness
THEOREM Spec => []OutputIsOnlyPossibleMajority
THEOREM Spec => Termination
=============================================================================