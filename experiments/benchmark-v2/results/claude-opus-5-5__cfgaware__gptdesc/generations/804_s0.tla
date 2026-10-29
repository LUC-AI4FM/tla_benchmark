--------------------------- MODULE BinarySearch ---------------------------
EXTENDS Integers, Sequences, FiniteSets, TLAPS

CONSTANT Values

ASSUME ValuesAssump == Values \subseteq Int

MaxLen == 4

BoundedSeqs(S) == UNION {[1..n -> S] : n \in 0..MaxLen}

SortedSeqs == {ss \in BoundedSeqs(Values) :
                  \A i, j \in 1..Len(ss) : (i < j) => (ss[i] =< ss[j])}

(***************************************************************************
--algorithm BinarySearch
variables seq \in SortedSeqs, val \in Values,
          low = 1, high = Len(seq), result = 0 ;
begin
a: while low =< high /\ result = 0 do
     with mid = (low + high) \div 2, mval = seq[mid] do
       if mval = val then result := mid
       elsif val < mval then high := mid - 1
       else low := mid + 1
       end if
     end with
   end while
end algorithm
***************************************************************************)
\* BEGIN TRANSLATION
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
           THEN /\ LET mid == (low + high) \div 2 IN
                     LET mval == seq[mid] IN
                       IF mval = val
                          THEN /\ result' = mid
                               /\ UNCHANGED << low, high >>
                          ELSE IF val < mval
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

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")
\* END TRANSLATION

-----------------------------------------------------------------------------

resultCorrect ==
   (pc = "Done") => IF val \in {seq[i] : i \in 1..Len(seq)}
                       THEN result \in 1..Len(seq) /\ seq[result] = val
                       ELSE result = 0

TypeOK == /\ seq \in SortedSeqs
          /\ val \in Values
          /\ low \in 1..(Len(seq) + 1)
          /\ high \in 0..Len(seq)
          /\ result \in 0..Len(seq)
          /\ pc \in {"a", "Done"}

Inv == /\ TypeOK
       /\ (result /= 0) => seq[result] = val
       /\ (result = 0) =>
             ((val \in {seq[i] : i \in 1..Len(seq)}) =>
                 \E i \in low..high : seq[i] = val)
       /\ (pc = "Done") => ((result /= 0) \/ (low > high))

THEOREM Correctness == Spec => []resultCorrect
<1>1. Init => Inv
  BY ValuesAssump DEF Init, Inv, TypeOK, SortedSeqs, BoundedSeqs
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <2>1. CASE a
    BY <2>1, ValuesAssump DEF Inv, TypeOK, a, SortedSeqs, BoundedSeqs
  <2>2. CASE Terminating
    BY <2>2 DEF Inv, TypeOK, Terminating, vars
  <2>3. CASE UNCHANGED vars
    BY <2>3 DEF Inv, TypeOK, vars
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Next
<1>3. Inv => resultCorrect
  BY ValuesAssump DEF Inv, TypeOK, resultCorrect, SortedSeqs, BoundedSeqs
<1>4. QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec

=============================================================================