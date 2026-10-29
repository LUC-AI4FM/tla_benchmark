---------------------------- MODULE MCBinarySearch ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

(***************************************************************************)
(* Model-checking bounds                                                   *)
(***************************************************************************)
MaxSeqLen == 8

LimitedSeq(S) == UNION { [1..n -> S] : n \in 0..MaxSeqLen }

Values == {1, 2, 3, 4, 5}

(***************************************************************************)
(* Binary search algorithm                                                 *)
(***************************************************************************)
Range(f) == { f[i] : i \in DOMAIN f }

SortedSeqs(S) == { s \in LimitedSeq(S) :
                     \A i, j \in 1..Len(s) : (i <= j) => (s[i] <= s[j]) }

VARIABLES seq, val, low, high, mid, result, pc

vars == << seq, val, low, high, mid, result, pc >>

Init ==
    /\ seq \in SortedSeqs(Values)
    /\ val \in Values
    /\ low = 1
    /\ high = Len(seq)
    /\ mid = 0
    /\ result = 0
    /\ pc = "a"

Step ==
    /\ pc = "a"
    /\ IF low <= high
         THEN LET m == (low + high) \div 2 IN
              /\ mid' = m
              /\ IF seq[m] = val
                   THEN /\ result' = m
                        /\ pc' = "Done"
                        /\ UNCHANGED << low, high >>
                   ELSE /\ IF seq[m] < val
                             THEN /\ low' = m + 1
                                  /\ UNCHANGED high
                             ELSE /\ high' = m - 1
                                  /\ UNCHANGED low
                        /\ UNCHANGED result
                        /\ pc' = "a"
         ELSE /\ pc' = "Done"
              /\ UNCHANGED << low, high, mid, result >>
    /\ UNCHANGED << seq, val >>

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == Step \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
TypeOK ==
    /\ seq \in LimitedSeq(Values)
    /\ val \in Values
    /\ low \in 1..(MaxSeqLen + 1)
    /\ high \in 0..MaxSeqLen
    /\ mid \in 0..MaxSeqLen
    /\ result \in 0..MaxSeqLen
    /\ pc \in {"a", "Done"}

Inv ==
    /\ result \in 0..Len(seq)
    /\ (result # 0) => (seq[result] = val)
    /\ (result = 0 /\ val \in Range(seq)) =>
           \E i \in low..high : seq[i] = val

resultCorrect ==
    (pc = "Done") =>
        IF val \in Range(seq)
          THEN result \in 1..Len(seq) /\ seq[result] = val
          ELSE result = 0

(***************************************************************************)
(* Liveness                                                                *)
(***************************************************************************)
Termination == <>(pc = "Done")

THEOREM Spec => [](TypeOK /\ Inv /\ resultCorrect)
THEOREM Spec => Termination
=============================================================================