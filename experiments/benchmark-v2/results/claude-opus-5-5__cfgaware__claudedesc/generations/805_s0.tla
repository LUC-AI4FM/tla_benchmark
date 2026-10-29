---------------------------- MODULE MCBinarySearch ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT Values

ASSUME Values \subseteq Int

MaxSeqLen == 8

LimitedSeq(S) == UNION { [1..n -> S] : n \in 0..MaxSeqLen }

Range(f) == { f[i] : i \in DOMAIN f }

IsSorted(s) == \A i, j \in 1..Len(s) : i <= j => s[i] <= s[j]

SortedSeqs == { s \in Seq(Values) : IsSorted(s) }

VARIABLES seq, val, low, high, result, pc

vars == << seq, val, low, high, result, pc >>

TypeOK ==
    /\ seq \in Seq(Values)
    /\ val \in Values
    /\ low \in 1..(Len(seq) + 1)
    /\ high \in 0..Len(seq)
    /\ result \in 0..Len(seq)
    /\ pc \in {"Lp", "Done"}

Init ==
    /\ seq \in SortedSeqs
    /\ val \in Values
    /\ low = 1
    /\ high = Len(seq)
    /\ result = 0
    /\ pc = "Lp"

Lp ==
    /\ pc = "Lp"
    /\ IF low <= high
         THEN LET mid == (low + high) \div 2 IN
                IF seq[mid] = val
                  THEN /\ result' = mid
                       /\ pc' = "Done"
                       /\ UNCHANGED << low, high >>
                  ELSE IF seq[mid] < val
                         THEN /\ low' = mid + 1
                              /\ UNCHANGED << high, result, pc >>
                         ELSE /\ high' = mid - 1
                              /\ UNCHANGED << low, result, pc >>
         ELSE /\ pc' = "Done"
              /\ UNCHANGED << low, high, result >>
    /\ UNCHANGED << seq, val >>

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == Lp \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Lp)

Inv ==
    /\ IsSorted(seq)
    /\ (pc = "Lp") =>
         /\ result = 0
         /\ (val \in Range(seq) =>
               \E i \in low..high : i \in 1..Len(seq) /\ seq[i] = val)

resultCorrect ==
    (pc = "Done") =>
        IF val \in Range(seq)
          THEN /\ result \in 1..Len(seq)
               /\ seq[result] = val
          ELSE result = 0

Termination == <>(pc = "Done")

=============================================================================