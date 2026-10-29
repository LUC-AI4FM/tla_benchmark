---------------------------- MODULE BinarySearch ----------------------------
EXTENDS Integers, Sequences

CONSTANT Values

ASSUME ValAssump == Values \subseteq Int

MaxLen == 3

\* All sorted sequences over Values up to length MaxLen
SortedSeqs ==
  { ss \in UNION { [1..n -> Values] : n \in 0..MaxLen } :
      \A i, j \in 1..Len(ss) : (i < j) => (ss[i] =< ss[j]) }

VARIABLES seq, val, low, high, result, pc

vars == << seq, val, low, high, result, pc >>

Init ==
  /\ seq \in SortedSeqs
  /\ val \in Values
  /\ low = 1
  /\ high = Len(seq)
  /\ result = 0
  /\ pc = "a"

a ==
  /\ pc = "a"
  /\ IF low =< high /\ result = 0
       THEN LET mid == (low + high) \div 2 IN
              /\ IF seq[mid] = val
                   THEN /\ result' = mid
                        /\ UNCHANGED << low, high >>
                   ELSE IF val < seq[mid]
                          THEN /\ high' = mid - 1
                               /\ UNCHANGED << low, result >>
                          ELSE /\ low' = mid + 1
                               /\ UNCHANGED << high, result >>
              /\ pc' = "a"
       ELSE /\ pc' = "Done"
            /\ UNCHANGED << low, high, result >>
  /\ UNCHANGED << seq, val >>

Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------

TypeOK ==
  /\ seq \in SortedSeqs
  /\ val \in Values
  /\ low \in 1..(Len(seq) + 1)
  /\ high \in 0..Len(seq)
  /\ result \in 0..Len(seq)
  /\ pc \in {"a", "Done"}

TargetInSeq == \E i \in 1..Len(seq) : seq[i] = val

Sorted == \A i, j \in 1..Len(seq) : (i < j) => (seq[i] =< seq[j])

Inv ==
  /\ TypeOK
  /\ Sorted
  /\ low =< high + 1
  /\ (result # 0) => (seq[result] = val)
  /\ (result = 0 /\ TargetInSeq) => (\E i \in low..high : seq[i] = val)

resultCorrect ==
  (pc = "Done") =>
     IF result # 0
       THEN seq[result] = val
       ELSE ~TargetInSeq

Termination == <>(pc = "Done")

=============================================================================