---------------------------- MODULE BinarySearch ----------------------------
EXTENDS Integers

CONSTANTS Values, MaxSeqLen

(* Sequence operators defined locally. Seq may be overridden by LimitedSeq. *)
Len(s) == CHOOSE n \in 0..MaxSeqLen + 1000 : DOMAIN s = 1..n

Seq(S) == UNION {[1..n -> S] : n \in Nat}

LimitedSeq(S) == UNION {[1..n -> S] : n \in 0..MaxSeqLen}

IsSorted(s) == \A i, j \in DOMAIN s : i <= j => s[i] <= s[j]

SortedSeqs == {s \in Seq(Values) : IsSorted(s)}

VARIABLES seq, target, low, high, result, pc

vars == <<seq, target, low, high, result, pc>>

TargetInSeq == \E i \in DOMAIN seq : seq[i] = target

Init ==
    /\ seq \in SortedSeqs
    /\ target \in Values
    /\ low = 1
    /\ high = Len(seq)
    /\ result = 0
    /\ pc = "search"

SearchStep ==
    /\ pc = "search"
    /\ low <= high
    /\ LET mid == (low + high) \div 2
       IN  IF seq[mid] = target
              THEN /\ result' = mid
                   /\ pc' = "done"
                   /\ UNCHANGED <<low, high>>
           ELSE IF seq[mid] < target
              THEN /\ low' = mid + 1
                   /\ UNCHANGED <<high, result, pc>>
           ELSE    /\ high' = mid - 1
                   /\ UNCHANGED <<low, result, pc>>
    /\ UNCHANGED <<seq, target>>

NotFound ==
    /\ pc = "search"
    /\ low > high
    /\ pc' = "done"
    /\ UNCHANGED <<seq, target, low, high, result>>

Terminating ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == SearchStep \/ NotFound \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------

TypeOK ==
    /\ seq \in Seq(Values)
    /\ IsSorted(seq)
    /\ target \in Values
    /\ low \in 1..(Len(seq) + 1)
    /\ high \in 0..Len(seq)
    /\ result \in 0..Len(seq)
    /\ pc \in {"search", "done"}

(* Soundness and completeness of the final result *)
resultCorrect ==
    /\ (result /= 0 => (result \in DOMAIN seq /\ seq[result] = target))
    /\ (TargetInSeq => result /= 0)

(* Search space invariant: while still searching, the target (if present)
   lies within the current bounds *)
SearchSpaceInv ==
    (pc = "search" /\ TargetInSeq) =>
        \E i \in low..high : i \in DOMAIN seq /\ seq[i] = target

Soundness ==
    result /= 0 => (result \in DOMAIN seq /\ seq[result] = target)

Inv ==
    /\ TypeOK
    /\ Soundness
    /\ SearchSpaceInv
    /\ (pc = "done" => resultCorrect)

Termination == <>(pc = "done")

=============================================================================