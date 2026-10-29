---------------------------- MODULE MCBinarySearch ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT Values
ASSUME Values \subseteq Int

CONSTANT MaxSeqLen
ASSUME MaxSeqLen \in Nat

LimitedSeq(S) == UNION {[1 .. n -> S] : n \in 1 .. MaxSeqLen}

SortedSeqs == {ss \in Seq(Values) :
                  \A i, j \in 1..Len(ss) : (i < j) => (ss[i] =< ss[j])}

Range(f) == {f[i] : i \in DOMAIN f}

(***************************************************************************
--algorithm BinarySearch
variables seq \in SortedSeqs, val \in Values,
          low = 1, high = Len(seq), result = 0 ;
begin
a: while low =< high /\ result = 0 do
     with mid = (low + high) \div 2 do
       if seq[mid] = val then result := mid
       elsif seq[mid] < val then low := mid + 1
       else high := mid - 1
       end if
     end with
   end while
end algorithm
***************************************************************************)

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
                      ELSE IF seq[mid] < val
                             THEN /\ low' = mid + 1
                                  /\ UNCHANGED << high, result >>
                             ELSE /\ high' = mid - 1
                                  /\ UNCHANGED << low, result >>
               /\ pc' = "a"
          ELSE /\ pc' = "Done"
               /\ UNCHANGED << low, high, result >>
     /\ UNCHANGED << seq, val >>

Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

resultCorrect ==
    (pc = "Done") =>
        IF val \in Range(seq)
          THEN result \in 1..Len(seq) /\ seq[result] = val
          ELSE result = 0

TypeOK == /\ seq \in SortedSeqs
          /\ val \in Values
          /\ low \in 1..(Len(seq) + 1)
          /\ high \in 0..Len(seq)
          /\ result \in 0..Len(seq)
          /\ pc \in {"a", "Done"}

Inv == /\ TypeOK
       /\ (result # 0) => (result \in 1..Len(seq) /\ seq[result] = val)
       /\ (result = 0 /\ val \in Range(seq)) =>
              \E i \in low..high : seq[i] = val
       /\ (pc = "Done") => (result # 0 \/ low > high)
       /\ resultCorrect
=============================================================================