---------------------------- MODULE BinarySearch ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLAPS

CONSTANT Values
ASSUME ValuesAssump == Values \subseteq Int /\ IsFiniteSet(Values)

IsSorted(ss) == \A i, j \in 1..Len(ss) : (i < j) => (ss[i] =< ss[j])

SortedSeqs == { ss \in UNION { [1..n -> Values] : n \in 0..Cardinality(Values) } :
                  IsSorted(ss) }

VARIABLES seq, val, low, high, result, pc

vars == << seq, val, low, high, result, pc >>

Init == /\ seq \in SortedSeqs
        /\ val \in Values
        /\ low = 1
        /\ high = Len(seq)
        /\ result = 0
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF low =< high /\ result = 0
          THEN LET mid == (low + high) \div 2 IN
                 /\ IF seq[mid] = val
                      THEN /\ result' = mid
                           /\ UNCHANGED << low, high >>
                      ELSE /\ IF val < seq[mid]
                                THEN /\ high' = mid - 1
                                     /\ low' = low
                                ELSE /\ low' = mid + 1
                                     /\ high' = high
                           /\ result' = result
                 /\ pc' = "a"
          ELSE /\ pc' = "Done"
               /\ UNCHANGED << low, high, result >>
     /\ UNCHANGED << seq, val >>

Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

-----------------------------------------------------------------------------

resultCorrect ==
  (pc = "Done") =>
     IF \E i \in 1..Len(seq) : seq[i] = val
       THEN result \in 1..Len(seq) /\ seq[result] = val
       ELSE result = 0

TypeOK == /\ seq \in Seq(Values)
          /\ IsSorted(seq)
          /\ val \in Values
          /\ low \in 1..(Len(seq) + 1)
          /\ high \in 0..Len(seq)
          /\ result \in 0..Len(seq)
          /\ pc \in {"a", "Done"}

Inv == /\ TypeOK
       /\ result # 0 => seq[result] = val
       /\ (result = 0 /\ \E i \in 1..Len(seq) : seq[i] = val)
             => \E i \in low..high : seq[i] = val
       /\ (pc = "Done" /\ result = 0) => low > high
       /\ low =< high + 1

-----------------------------------------------------------------------------

LEMMA SortedSeqsType == SortedSeqs \subseteq Seq(Values)
  <1>1. \A n \in 0..Cardinality(Values) : [1..n -> Values] \subseteq Seq(Values)
    BY ValuesAssump, FS_CardinalityType DEF Seq
  <1>. QED BY <1>1 DEF SortedSeqs

THEOREM InitInv == Init => Inv
  <1>. SUFFICES ASSUME Init PROVE Inv
    OBVIOUS
  <1>1. seq \in Seq(Values) /\ IsSorted(seq)
    BY SortedSeqsType DEF Init, SortedSeqs
  <1>. QED BY <1>1 DEF Init, Inv, TypeOK

THEOREM NextInv == Inv /\ [Next]_vars => Inv'
  <1>. SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <1>. USE ValuesAssump
  <1>0. seq \in Seq(Values) /\ IsSorted(seq) /\ val \in Values
    BY DEF Inv, TypeOK
  <1>1. CASE a
    <2>1. CASE low =< high /\ result = 0
      <2>. DEFINE mid == (low + high) \div 2
      <2>a. mid \in low..high /\ mid \in 1..Len(seq)
        BY <2>1 DEF Inv, TypeOK
      <2>b. seq[mid] \in Int
        BY <2>a, <1>0
      <2>2. CASE seq[mid] = val
        BY <1>1, <2>1, <2>2, <2>a, <1>0 DEF a, Inv, TypeOK
      <2>3. CASE seq[mid] # val /\ val < seq[mid]
        <3>1. \A i \in mid..high : seq[i] # val
          BY <2>a, <2>3, <1>0 DEF IsSorted, Inv, TypeOK
        <3>. QED BY <1>1, <2>1, <2>3, <2>a, <3>1, <1>0 DEF a, Inv, TypeOK
      <2>4. CASE seq[mid] # val /\ ~(val < seq[mid])
        <3>1. \A i \in low..mid : seq[i] # val
          BY <2>a, <2>4, <1>0 DEF IsSorted, Inv, TypeOK
        <3>. QED BY <1>1, <2>1, <2>4, <2>a, <3>1, <1>0 DEF a, Inv, TypeOK
      <2>. QED BY <2>2, <2>3, <2>4
    <2>2. CASE ~(low =< high /\ result = 0)
      BY <1>1, <2>2 DEF a, Inv, TypeOK
    <2>. QED BY <2>1, <2>2
  <1>2. CASE Terminating
    BY <1>2 DEF Terminating, vars, Inv, TypeOK
  <1>3. CASE UNCHANGED vars
    BY <1>3 DEF vars, Inv, TypeOK
  <1>. QED BY <1>1, <1>2, <1>3 DEF Next

THEOREM InvCorrect == Inv => resultCorrect
  <1>. SUFFICES ASSUME Inv, pc = "Done"
               PROVE  IF \E i \in 1..Len(seq) : seq[i] = val
                        THEN result \in 1..Len(seq) /\ seq[result] = val
                        ELSE result = 0
    BY DEF resultCorrect
  <1>1. CASE result # 0
    BY <1>1 DEF Inv, TypeOK
  <1>2. CASE result = 0
    BY <1>2 DEF Inv, TypeOK
  <1>. QED BY <1>1, <1>2

THEOREM Correctness == Spec => []resultCorrect
  <1>1. Init => Inv
    BY InitInv
  <1>2. Inv /\ [Next]_vars => Inv'
    BY NextInv
  <1>3. Inv => resultCorrect
    BY InvCorrect
  <1>. QED BY <1>1, <1>2, <1>3, PTL DEF Spec

=============================================================================