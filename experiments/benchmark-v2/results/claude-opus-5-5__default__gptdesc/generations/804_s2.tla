------------------------------ MODULE BinarySearch ------------------------------
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
         with (mid = (low + high) \div 2) {
           if (seq[mid] = val) { result := mid }
           else if (seq[mid] < val) { low := mid + 1 }
           else { high := mid - 1 }
         }
       }
  }
}
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
                     IF seq[mid] = val
                        THEN /\ result' = mid
                             /\ UNCHANGED << low, high >>
                        ELSE /\ IF seq[mid] < val
                                   THEN /\ low' = mid + 1
                                        /\ high' = high
                                   ELSE /\ high' = mid - 1
                                        /\ low' = low
                             /\ UNCHANGED result
                /\ pc' = "a"
           ELSE /\ pc' = "Done"
                /\ UNCHANGED << low, high, result >>
     /\ UNCHANGED << seq, val >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a
           \/ Terminating

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
       /\ (result # 0) => (seq[result] = val)
       /\ (\E i \in 1..Len(seq) : seq[i] = val) =>
             ((result # 0) \/ (\E i \in low..high : seq[i] = val))
       /\ (pc = "Done") => ((result # 0) \/ (low > high))

THEOREM Spec => []resultCorrect
<1>1. Init => Inv
  BY ValAssump DEF Init, Inv, TypeOK, SortedSeqs
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <2> USE ValAssump DEF Inv, TypeOK, SortedSeqs
  <2>1. CASE a
    <3>1. CASE low =< high /\ result = 0
      <4> DEFINE mid == (low + high) \div 2
      <4>1. mid \in low..high /\ mid \in 1..Len(seq)
        BY <3>1
      <4>2. seq[mid] \in Int
        BY <4>1
      <4>3. CASE seq[mid] = val
        BY <2>1, <3>1, <4>1, <4>3 DEF a
      <4>4. CASE seq[mid] < val
        BY <2>1, <3>1, <4>1, <4>2, <4>3, <4>4 DEF a
      <4>5. CASE seq[mid] > val
        BY <2>1, <3>1, <4>1, <4>2, <4>3, <4>5 DEF a
      <4> QED
        BY <4>2, <4>3, <4>4, <4>5
    <3>2. CASE ~(low =< high /\ result = 0)
      BY <2>1, <3>2 DEF a
    <3> QED
      BY <3>1, <3>2
  <2>2. CASE Terminating
    BY <2>2 DEF Terminating, vars
  <2>3. CASE UNCHANGED vars
    BY <2>3 DEF vars
  <2> QED
    BY <2>1, <2>2, <2>3 DEF Next
<1>3. Inv => resultCorrect
  BY DEF Inv, TypeOK, resultCorrect
<1>4. QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec

=============================================================================