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

Init == (* Global variables *)
        /\ seq \in SortedSeqs
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

Next == a
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")
\* END TRANSLATION

-----------------------------------------------------------------------------
(***************************************************************************)
(* Correctness: upon termination, result is an index of val in seq if val  *)
(* occurs in seq, and 0 otherwise.                                         *)
(***************************************************************************)
resultCorrect ==
   (pc = "Done") => IF \E i \in 1..Len(seq) : seq[i] = val
                      THEN seq[result] = val
                      ELSE result = 0

(***************************************************************************)
(* Inductive invariant.                                                    *)
(***************************************************************************)
Inv == /\ seq \in SortedSeqs
       /\ val \in Values
       /\ low \in 1..(Len(seq) + 1)
       /\ high \in 0..Len(seq)
       /\ result \in 0..Len(seq)
       /\ pc \in {"a", "Done"}
       /\ (result /= 0) => (result \in 1..Len(seq) /\ seq[result] = val)
       /\ (result = 0) =>
             ((\E i \in 1..Len(seq) : seq[i] = val) =>
                 (\E i \in low..high : seq[i] = val))
       /\ (pc = "Done") => (result /= 0 \/ low > high)

THEOREM InitInv == Init => Inv
  BY ValAssump DEF Init, Inv, SortedSeqs

THEOREM NextInv == Inv /\ [Next]_vars => Inv'
<1> SUFFICES ASSUME Inv, [Next]_vars
             PROVE  Inv'
  OBVIOUS
<1> USE ValAssump DEF Inv, SortedSeqs
<1>1. CASE a
  <2>1. CASE low =< high /\ result = 0
    <3> DEFINE mid == (low + high) \div 2
    <3>1. mid \in low..high /\ mid \in 1..Len(seq)
      BY <2>1
    <3>2. seq[mid] \in Int /\ val \in Int
      BY <3>1
    <3>3. CASE seq[mid] = val
      BY <1>1, <2>1, <3>1, <3>3 DEF a
    <3>4. CASE seq[mid] /= val /\ val < seq[mid]
      <4>1. \A i \in mid..high : seq[i] /= val
        BY <3>1, <3>2, <3>4
      <4>2. QED
        BY <1>1, <2>1, <3>1, <3>2, <3>4, <4>1 DEF a
    <3>5. CASE seq[mid] /= val /\ ~(val < seq[mid])
      <4>1. \A i \in low..mid : seq[i] /= val
        BY <3>1, <3>2, <3>5
      <4>2. QED
        BY <1>1, <2>1, <3>1, <3>2, <3>5, <4>1 DEF a
    <3>6. QED
      BY <3>3, <3>4, <3>5
  <2>2. CASE ~(low =< high /\ result = 0)
    BY <1>1, <2>2 DEF a
  <2>3. QED
    BY <2>1, <2>2
<1>2. CASE Terminating
  BY <1>2 DEF Terminating, vars
<1>3. CASE UNCHANGED vars
  BY <1>3 DEF vars
<1>4. QED
  BY <1>1, <1>2, <1>3 DEF Next

THEOREM InvCorrect == Inv => resultCorrect
  BY DEF Inv, resultCorrect, SortedSeqs

THEOREM Correctness == Spec => []resultCorrect
<1>1. Init => Inv
  BY InitInv
<1>2. Inv /\ [Next]_vars => Inv'
  BY NextInv
<1>3. Inv => resultCorrect
  BY InvCorrect
<1>4. QED
  BY <1>1, <1>2, <1>3, PTL DEF Spec

=============================================================================