---------------------------- MODULE BinarySearch ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANT Values

ASSUME ValuesAssump == /\ Values \subseteq Int
                       /\ IsFiniteSet(Values)

MaxLen == Cardinality(Values) + 1

SortedSeqs ==
  { ss \in UNION { [1..n -> Values] : n \in 0..MaxLen } :
      \A i, j \in 1..Len(ss) : i < j => ss[i] =< ss[j] }

VARIABLES seq, val, low, high, result, pc

vars == << seq, val, low, high, result, pc >>

TypeOK ==
  /\ seq \in SortedSeqs
  /\ val \in Values
  /\ low \in 1..(Len(seq) + 1)
  /\ high \in 0..Len(seq)
  /\ result \in 0..Len(seq)
  /\ pc \in {"a", "Done"}

Init ==
  /\ seq \in SortedSeqs
  /\ val \in Values
  /\ low = 1
  /\ high = Len(seq)
  /\ result = 0
  /\ pc = "a"

a ==
  /\ pc = "a"
  /\ IF low =< high
       THEN LET mid == (low + high) \div 2
            IN  IF seq[mid] = val
                  THEN /\ result' = mid
                       /\ pc' = "Done"
                       /\ UNCHANGED << low, high >>
                  ELSE /\ IF seq[mid] < val
                            THEN /\ low' = mid + 1
                                 /\ high' = high
                            ELSE /\ high' = mid - 1
                                 /\ low' = low
                       /\ pc' = "a"
                       /\ result' = result
       ELSE /\ pc' = "Done"
            /\ UNCHANGED << low, high, result >>
  /\ UNCHANGED << seq, val >>

Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

ValInSeq == \E i \in 1..Len(seq) : seq[i] = val

resultCorrect ==
  (pc = "Done") =>
     IF ValInSeq
       THEN result \in 1..Len(seq) /\ seq[result] = val
       ELSE result = 0

Inv ==
  /\ TypeOK
  /\ (result /= 0) => (result \in 1..Len(seq) /\ seq[result] = val)
  /\ (pc = "a") => (result = 0)
  /\ (ValInSeq /\ result = 0) => (\E i \in low..high : seq[i] = val)
  /\ resultCorrect
=============================================================================