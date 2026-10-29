---------------------------- MODULE BinarySearch ----------------------------
EXTENDS Integers, Sequences, TLAPS

CONSTANT Values
ASSUME ValAssump == Values \subseteq Int

SortedSeqs == {ss \in Seq(Values) :
                 \A i, j \in 1..Len(ss) : (i < j) => (ss[i] =< ss[j])}

(***************************************************************************
--fair algorithm BinarySearch {
  variables seq \in SortedSeqs, val \in Values,
            low = 1, high = Len(seq), result = 0 ;
  { a: while (low =< high /\ result = 0) {
         with (mid = (low + high) \div 2, mval = seq[mid]) {
           if (mval = val) { result := mid }
           else if (val < mval) { high := mid - 1 }
           else { low := mid + 1 } } } } }
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
                          ELSE /\ IF val < mval
                                     THEN /\ high' = mid - 1
                                          /\ low' = low
                                     ELSE /\ low' = mid + 1
                                          /\ high' = high
                               /\ UNCHANGED result
                /\ pc' = "a"
           ELSE /\ pc' = "Done"
                /\ UNCHANGED << low, high, result >>
     /\ UNCHANGED << seq, val >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")
\* END TRANSLATION

-----------------------------------------------------------------------------
resultCorrect ==
   (pc = "Done") => IF \E i \in 1..Len(seq) : seq[i] = val
                      THEN seq[result] = val
                      ELSE result = 0

TypeOK == /\ seq \in SortedSeqs
          /\ val \in Values
          /\ low \in 1..(Len(seq) + 1)
          /\ high \in 0..Len(seq)
          /\ result \in 0..Len(seq)
          /\ pc \in {"a", "Done"}

Inv == /\ TypeOK
       /\ (result /= 0) => (Len(seq) > 0) /\ (seq[result] = val)
       /\ (pc = "a") => IF \E i \in 1..Len(seq) : seq[i] = val
                          THEN \E i \in low..high : seq[i] = val
                          ELSE result = 0
       /\ (pc = "Done") => \/ result /= 0
                           \/ \A i \in 1..Len(seq) : seq[i] /= val

THEOREM Spec => []resultCorrect
<1>1. Init => Inv
  BY ValAssump DEF Init, Inv, TypeOK, SortedSeqs
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv,
                      [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <2> USE DEF Inv, TypeOK
  <2>1. ASSUME a
        PROVE  Inv'
    <3> USE <2>1 DEF a
    <3>1. CASE low =< high /\ result = 0
      <4> DEFINE mid == (low + high) \div 2
      <4> DEFINE mval == seq[mid]
      <4>1. mid \in low..high /\ mid \in 1..Len(seq)
        BY <3>1
      <4>2. mval \in Int
        BY <4>1, ValAssump DEF SortedSeqs
      <4>3. val \in Int
        BY ValAssump
      <4>4. CASE mval = val
        BY <3>1, <4>1, <4>4
      <4>5. CASE mval /= val /\ val < mval
        BY <3>1, <4>1, <4>2, <4>3, <4>5, ValAssump DEF SortedSeqs
      <4>6. CASE mval /= val /\ ~(val < mval)
        BY <3>1, <4>1, <4>2, <4>3, <4>6, ValAssump DEF SortedSeqs
      <4>7. QED
        BY <4>4, <4>5, <4>6
    <3>2. CASE ~(low =< high /\ result = 0)
      BY <3>2
    <3>3. QED
      BY <3>1, <3>2
  <2>2. CASE UNCHANGED vars
    BY <2>2 DEF vars
  <2>3. ASSUME Terminating
        PROVE  Inv'
    BY <2>3 DEF Terminating, vars
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Next
<1>3. Inv => resultCorrect
  BY DEF Inv, TypeOK, resultCorrect
<1>4. QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec

=============================================================================