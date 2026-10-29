---------------------------- MODULE BinarySearch ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    Values,     \* finite set of integers the sequence elements and target are drawn from
    MaxLen      \* maximum length of the input sequence

ASSUME ValuesAssumption == Values \subseteq Int /\ Values # {}
ASSUME MaxLenAssumption == MaxLen \in Nat

VARIABLES
    seq,        \* the sorted input sequence
    target,     \* the value being searched for
    low,        \* lower bound of the current search range (inclusive)
    high,       \* upper bound of the current search range (inclusive)
    result,     \* returned index (0 means "not found")
    pc          \* program counter: "loop" or "done"

vars == << seq, target, low, high, result, pc >>

-----------------------------------------------------------------------------
(* Helper definitions *)

IsSorted(s) == \A i, j \in 1..Len(s) : i <= j => s[i] <= s[j]

\* All sorted sequences of length 0..MaxLen over Values
SortedSeqs ==
    UNION { { s \in [1..n -> Values] : \A i, j \in 1..n : i <= j => s[i] <= s[j] }
            : n \in 0..MaxLen }

\* The target occurs somewhere in the sequence
TargetInSeq == \E i \in 1..Len(seq) : seq[i] = target

\* Overflow-safe midpoint computation (mirrors a correct implementation)
Mid(l, h) == l + ((h - l) \div 2)

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ seq \in SortedSeqs
    /\ target \in Values
    /\ low = 1
    /\ high = Len(seq)
    /\ result = 0
    /\ pc = "loop"

-----------------------------------------------------------------------------
(* Actions *)

\* One iteration of the loop while the search range is non-empty
Step ==
    /\ pc = "loop"
    /\ low <= high
    /\ LET m == Mid(low, high) IN
         IF seq[m] = target
           THEN /\ result' = m
                /\ pc' = "done"
                /\ UNCHANGED << low, high >>
         ELSE IF seq[m] < target
           THEN /\ low' = m + 1
                /\ UNCHANGED << high, result, pc >>
         ELSE /\ high' = m - 1
              /\ UNCHANGED << low, result, pc >>
    /\ UNCHANGED << seq, target >>

\* Search range is empty: target is absent, report "not found" (0)
NotFound ==
    /\ pc = "loop"
    /\ low > high
    /\ result' = 0
    /\ pc' = "done"
    /\ UNCHANGED << seq, target, low, high >>

\* Terminal state: allow stuttering to avoid deadlock reports
Terminated ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == Step \/ NotFound \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Step \/ NotFound)

-----------------------------------------------------------------------------
(* Safety properties *)

\* Type safety: all variables have expected types and indices stay in bounds
TypeOK ==
    /\ seq \in Seq(Values)
    /\ IsSorted(seq)
    /\ target \in Values
    /\ low \in 1..(Len(seq) + 1)
    /\ high \in 0..Len(seq)
    /\ result \in 0..Len(seq)
    /\ pc \in {"loop", "done"}

\* Any index used to access the sequence is within its valid range
IndexSafety ==
    /\ (pc = "loop" /\ low <= high) =>
          /\ 1 <= low
          /\ high <= Len(seq)
          /\ Mid(low, high) \in 1..Len(seq)
          /\ low <= Mid(low, high) /\ Mid(low, high) <= high
    /\ (result # 0) => result \in 1..Len(seq)

\* Key loop invariant: if the target exists, it remains within [low, high]
BoundsInvariant ==
    (pc = "loop" /\ TargetInSeq) =>
        \E i \in low..high : seq[i] = target

\* Stronger form: elements outside [low, high] are known not to be the target
ExcludedInvariant ==
    pc = "loop" =>
        /\ \A i \in 1..(low - 1) : seq[i] < target
        /\ \A i \in (high + 1)..Len(seq) : seq[i] > target

\* Partial correctness: on termination the result is correct
PartialCorrectness ==
    pc = "done" =>
        IF result # 0
          THEN /\ result \in 1..Len(seq)
               /\ seq[result] = target
          ELSE ~TargetInSeq

\* The input is never modified
InputUnchanged == [][UNCHANGED << seq, target >>]_vars

\* The search range strictly shrinks on each non-terminating loop step
RangeShrinks ==
    [][ (pc = "loop" /\ pc' = "loop") =>
           (high' - low') < (high - low) ]_vars

-----------------------------------------------------------------------------
(* Liveness properties *)

\* Termination: the algorithm eventually completes
Termination == <>(pc = "done")

\* Once done, the algorithm stays done with a fixed result
StableResult == [][pc = "done" => (pc' = "done" /\ result' = result)]_vars

=============================================================================