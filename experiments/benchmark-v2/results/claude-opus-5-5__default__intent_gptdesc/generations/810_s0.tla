---------------------------- MODULE BoyerMooreMajority ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Value,      \* the fixed set of three possible input values
    MaxLen,     \* bound on input sequence length
    NoCand      \* distinguished "no candidate" marker

ASSUME ValueAssumption  == Cardinality(Value) = 3
ASSUME MaxLenAssumption == MaxLen \in Nat
ASSUME NoCandAssumption == NoCand \notin Value

VARIABLES
    seq,    \* the nondeterministically chosen input sequence
    i,      \* index of the next element to process
    cand,   \* current candidate
    cnt,    \* current counter
    pc      \* phase: "choose", "run", "done"

vars == <<seq, i, cand, cnt, pc>>

-----------------------------------------------------------------------------------
(* Helpers *)

\* All sequences over Value of length 0..MaxLen
BoundedSeqs == UNION { [1..n -> Value] : n \in 0..MaxLen }

\* Number of occurrences of v among the first k positions of s
CountPrefix(s, v, k) == Cardinality({ j \in 1..k : s[j] = v })

\* Number of occurrences of v in the entire sequence s
Count(s, v) == CountPrefix(s, v, Len(s))

\* v is a strict majority element of s
IsMajority(s, v) == 2 * Count(s, v) > Len(s)

-----------------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ seq  = << >>
    /\ i    = 1
    /\ cand = NoCand
    /\ cnt  = 0
    /\ pc   = "choose"

(* Nondeterministically choose an input sequence of any length 0..MaxLen *)
ChooseInput ==
    /\ pc = "choose"
    /\ \E s \in BoundedSeqs : seq' = s
    /\ pc' = "run"
    /\ UNCHANGED <<i, cand, cnt>>

(* One step of the majority-vote procedure *)
Step ==
    /\ pc = "run"
    /\ i <= Len(seq)
    /\ IF cnt = 0
         THEN /\ cand' = seq[i]
              /\ cnt'  = 1
         ELSE IF cand = seq[i]
                THEN /\ cnt'  = cnt + 1
                     /\ cand' = cand
                ELSE /\ cnt'  = cnt - 1
                     /\ cand' = cand
    /\ i' = i + 1
    /\ UNCHANGED <<seq, pc>>

(* All elements processed *)
Finish ==
    /\ pc = "run"
    /\ i > Len(seq)
    /\ pc' = "done"
    /\ UNCHANGED <<seq, i, cand, cnt>>

(* Terminal stuttering to avoid reporting deadlock *)
Terminated ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == ChooseInput \/ Step \/ Finish \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------------
(* Safety invariants *)

TypeOK ==
    /\ seq  \in BoundedSeqs
    /\ i    \in 1..(MaxLen + 1)
    /\ i    <= Len(seq) + 1
    /\ cand \in Value \cup {NoCand}
    /\ cnt  \in Nat
    /\ pc   \in {"choose", "run", "done"}

CounterNonNegative == cnt >= 0

CandidateWellFormed == cand \in Value \cup {NoCand}

\* NoCand only while the counter is zero
NoCandImpliesZero == (cand = NoCand) => (cnt = 0)

\* Inductive invariant on the processed prefix (positions 1..i-1)
PrefixInvariant ==
    pc \in {"run", "done"} =>
        \A v \in Value :
            IF v = cand
              THEN 2 * CountPrefix(seq, v, i - 1) <= (i - 1) + cnt
              ELSE 2 * CountPrefix(seq, v, i - 1) <= (i - 1) - cnt

\* Main correctness property: if a strict majority exists, candidate equals it
MajorityCorrect ==
    pc = "done" =>
        \A v \in Value : IsMajority(seq, v) => cand = v

-----------------------------------------------------------------------------------
(* Action property: counter/candidate change only by allowed update rules *)

AllowedUpdate ==
    \/ /\ cnt = 0
       /\ cand' = seq[i]
       /\ cnt'  = 1
    \/ /\ cnt > 0
       /\ cand = seq[i]
       /\ cand' = cand
       /\ cnt'  = cnt + 1
    \/ /\ cnt > 0
       /\ cand # seq[i]
       /\ cand' = cand
       /\ cnt'  = cnt - 1

UpdateRules ==
    [][ (<<cand, cnt>>' # <<cand, cnt>>) =>
          /\ pc = "run"
          /\ i <= Len(seq)
          /\ i' = i + 1
          /\ seq' = seq
          /\ AllowedUpdate ]_vars

\* Once an input is chosen, it never changes
InputStable ==
    [][ pc # "choose" => seq' = seq ]_vars

-----------------------------------------------------------------------------------
(* Liveness *)

Termination == <>(pc = "done")

EventuallyCorrect ==
    <>(pc = "done" /\ \A v \in Value : IsMajority(seq, v) => cand = v)

-----------------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ CounterNonNegative /\ CandidateWellFormed
                    /\ NoCandImpliesZero /\ PrefixInvariant /\ MajorityCorrect)
THEOREM Spec => UpdateRules /\ InputStable
THEOREM Spec => Termination /\ EventuallyCorrect

===================================================================================