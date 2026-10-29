---------------------------- MODULE BinarySearch ----------------------------
EXTENDS Integers

CONSTANTS Values,     \* set of comparable (integer) keys
          MaxSeqLen   \* maximum allowed length of the input sequence

ASSUME /\ MaxSeqLen \in Nat
       /\ MaxSeqLen >= 1
       /\ Values \subseteq Int

-----------------------------------------------------------------------------
(* Sequences are defined locally rather than through EXTENDS Sequences, so  *)
(* that the module itself can define the name Seq.                          *)

Seq(S) == UNION {[1..n -> S] : n \in Nat}

\* All nonempty sequences over S whose length is at most MaxSeqLen.
LimitedSeq(S) == UNION {[1..n -> S] : n \in 1..MaxSeqLen}

Len(s) == CHOOSE n \in 0..MaxSeqLen : DOMAIN s = 1..n

Range(s) == {s[i] : i \in DOMAIN s}

IsSorted(s) == \A i, j \in DOMAIN s : i < j => s[i] <= s[j]

\* Duplicates are allowed.
SortedSeqs == {ss \in LimitedSeq(Values) : IsSorted(ss)}

-----------------------------------------------------------------------------
VARIABLES seq,     \* the input sequence (fixed after initialization)
          val,     \* the target key
          low,     \* lower bound of the current search interval
          high,    \* upper bound of the current search interval
          result,  \* 0 = not found, otherwise an index at which val occurs
          pc       \* control state: "search" or "Done"

vars == <<seq, val, low, high, result, pc>>

-----------------------------------------------------------------------------
Init == /\ seq \in SortedSeqs
        /\ val \in Values
        /\ low = 1
        /\ high = Len(seq)
        /\ result = 0
        /\ pc = "search"

\* One probe of the midpoint of a nonempty interval.
Probe == /\ pc = "search"
         /\ low <= high
         /\ LET mid == (low + high) \div 2 IN
              IF seq[mid] = val
                THEN /\ result' = mid
                     /\ pc' = "Done"
                     /\ UNCHANGED <<low, high>>
                ELSE /\ IF seq[mid] < val
                          THEN /\ low' = mid + 1
                               /\ UNCHANGED high
                          ELSE /\ high' = mid - 1
                               /\ UNCHANGED low
                     /\ UNCHANGED <<result, pc>>
         /\ UNCHANGED <<seq, val>>

\* The interval is empty, so report failure deterministically.
NotFound == /\ pc = "search"
            /\ low > high
            /\ result' = 0
            /\ pc' = "Done"
            /\ UNCHANGED <<seq, val, low, high>>

\* After termination, stutter so the behavior is not deadlocked.
Terminated == /\ pc = "Done"
              /\ UNCHANGED vars

Next == Probe \/ NotFound \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Probe \/ NotFound)

-----------------------------------------------------------------------------
TypeOK == /\ seq \in LimitedSeq(Values)
          /\ val \in Values
          /\ low \in 1..(MaxSeqLen + 1)
          /\ high \in 0..MaxSeqLen
          /\ result \in 0..MaxSeqLen
          /\ pc \in {"search", "Done"}

\* Correctness of the final result: found iff the key is a member, and any
\* reported index is in bounds and points to an element equal to the target.
resultCorrect ==
    pc = "Done" =>
        /\ (result # 0) <=> (val \in Range(seq))
        /\ result # 0 => /\ result \in 1..Len(seq)
                         /\ seq[result] = val

\* The interval bounds stay within the limits of the sequence.
BoundsOK == /\ low \in 1..(Len(seq) + 1)
            /\ high \in 0..Len(seq)
            /\ low <= high + 1

\* If the target is present, it lies within the current search interval.
TargetInInterval ==
    (pc = "search" /\ val \in Range(seq)) =>
        \E i \in low..high : seq[i] = val

\* No out-of-bounds access: every midpoint probed is a valid index.
SafeAccess ==
    (pc = "search" /\ low <= high) => ((low + high) \div 2) \in 1..Len(seq)

\* Only valid indices are returned.
ValidResult == result # 0 => (result \in 1..Len(seq) /\ seq[result] = val)

Inv == /\ TypeOK
       /\ IsSorted(seq)
       /\ BoundsOK
       /\ TargetInInterval
       /\ SafeAccess
       /\ ValidResult
       /\ resultCorrect

\* The search interval strictly decreases on every step that continues
\* the search.
IntervalSize == high - low + 1

IntervalDecreases ==
    [][(pc = "search" /\ pc' = "search") => IntervalSize' < IntervalSize]_vars

\* The search terminates on every input within the bounded size.
Termination == <>(pc = "Done")

\* Once the search has terminated, its result is correct.
EventuallyCorrect == <>[](pc = "Done" /\ resultCorrect)

THEOREM Spec => [](Inv) /\ IntervalDecreases /\ Termination
=============================================================================