------------------------------ MODULE BinarySearch ------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    Values,     \* finite set of integers that sequence elements and target range over
    MaxLen      \* maximum length of the input sequence

ASSUME ValuesAssump == Values \subseteq Int /\ IsFiniteSet(Values) /\ Values # {}
ASSUME MaxLenAssump == MaxLen \in Nat

VARIABLES
    seq,        \* the (sorted) input sequence
    target,     \* the value being searched for
    lo,         \* inclusive lower bound of the current search interval
    hi,         \* inclusive upper bound of the current search interval
    result,     \* 0 = not (yet) found / not present; otherwise index of found element
    pc          \* control state: "loop" or "done"

vars == <<seq, target, lo, hi, result, pc>>

-----------------------------------------------------------------------------
(* Helper definitions *)

Sorted(s) == \A i, j \in 1..Len(s) : i <= j => s[i] <= s[j]

AllSeqs == UNION { [1..n -> Values] : n \in 0..MaxLen }

SortedSeqs == { s \in AllSeqs : Sorted(s) }

N == Len(seq)

TargetInSeq == \E i \in 1..N : seq[i] = target

TargetInBounds == \E i \in lo..hi : seq[i] = target

Mid == (lo + hi) \div 2

-----------------------------------------------------------------------------
(* Initial state: any sorted sequence and any target from the domain *)

Init ==
    /\ seq \in SortedSeqs
    /\ target \in Values
    /\ lo = 1
    /\ hi = Len(seq)
    /\ result = 0
    /\ pc = "loop"

-----------------------------------------------------------------------------
(* Actions *)

\* Examine the middle element of the non-empty current interval.
Search ==
    /\ pc = "loop"
    /\ lo <= hi
    /\ IF seq[Mid] = target
          THEN /\ result' = Mid
               /\ pc' = "done"
               /\ UNCHANGED <<lo, hi>>
       ELSE IF seq[Mid] < target
          THEN /\ lo' = Mid + 1
               /\ UNCHANGED <<hi, result, pc>>
          ELSE /\ hi' = Mid - 1
               /\ UNCHANGED <<lo, result, pc>>
    /\ UNCHANGED <<seq, target>>

\* Bounds have crossed: target is not present.
NotFound ==
    /\ pc = "loop"
    /\ lo > hi
    /\ pc' = "done"
    /\ UNCHANGED <<seq, target, lo, hi, result>>

\* Terminal state: allow stuttering so behaviors are infinite.
Terminated ==
    /\ pc = "done"
    /\ UNCHANGED vars

Step == Search \/ NotFound

Next == Step \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK ==
    /\ seq \in SortedSeqs
    /\ target \in Values
    /\ lo \in Int
    /\ hi \in Int
    /\ result \in 0..Len(seq)
    /\ pc \in {"loop", "done"}

\* Bounds lie within or immediately adjacent to the valid index range,
\* and form a contiguous interval, or are adjacent (lo = hi + 1) when empty.
BoundsOK ==
    /\ lo \in 1..(N + 1)
    /\ hi \in 0..N
    /\ lo <= hi + 1

\* Result is either zero or a valid index of a matching element.
ResultOK ==
    /\ result \in 0..N
    /\ result # 0 => (result \in 1..N /\ seq[result] = target)

\* Sortedness is preserved.
SortedInv == Sorted(seq)

\* Narrowing preserves existence of the target within the current bounds.
ContainmentInv ==
    (TargetInSeq /\ result = 0) => TargetInBounds

\* Nonexistence is preserved as well: anything in bounds is in the sequence.
NonExistenceInv ==
    ~TargetInSeq => (result = 0 /\ ~TargetInBounds)

\* Partial correctness.
PartialCorrectness ==
    pc = "done" =>
        /\ (result # 0 => seq[result] = target)
        /\ (result = 0 => \A i \in 1..N : seq[i] # target)

Inv ==
    /\ TypeOK
    /\ BoundsOK
    /\ ResultOK
    /\ SortedInv
    /\ ContainmentInv
    /\ NonExistenceInv
    /\ PartialCorrectness

-----------------------------------------------------------------------------
(* Temporal properties *)

\* The input sequence and target never change.
InputUnchanged == [][seq' = seq /\ target' = target]_vars

\* Sortedness holds throughout.
SortednessPreserved == []Sorted(seq)

\* Once terminated, the state stays terminated.
DoneStable == [][pc = "done" => pc' = "done"]_vars

\* The search interval never grows while looping.
IntervalShrinks ==
    [][(pc = "loop" /\ pc' = "loop") => (hi' - lo' < hi - lo)]_vars

\* Termination: eventually reach a terminal state.
Termination == <>(pc = "done")

\* Termination with a correct outcome.
EventuallyCorrect ==
    <>( /\ pc = "done"
        /\ (result # 0 => seq[result] = target)
        /\ (result = 0 => ~TargetInSeq) )

\* If the target occurs, it is eventually found.
FoundIfPresent == TargetInSeq ~> (pc = "done" /\ result # 0)

-----------------------------------------------------------------------------
THEOREM Spec => []Inv
THEOREM Spec => Termination
THEOREM Spec => EventuallyCorrect
THEOREM Spec => FoundIfPresent
THEOREM Spec => InputUnchanged /\ SortednessPreserved /\ DoneStable /\ IntervalShrinks
=============================================================================