------------------------------ MODULE BinarySearch ------------------------------
(***************************************************************************)
(* A high-level model of classical binary search over finite, sorted,      *)
(* nonempty sequences of comparable (integer) keys whose length is bounded *)
(* by MaxLen.  The input sequence and the target key are chosen            *)
(* nondeterministically in the initial state, so every valid input within  *)
(* the bound is covered.  Duplicates are allowed.                          *)
(*                                                                         *)
(* Result convention: result = 0 means "not found" (deterministic failure),*)
(* otherwise result is an index i with seq[i] = target.                    *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    MaxLen,     \* maximum allowed sequence length
    Values      \* finite set of comparable keys

ASSUME MaxLenAssump == MaxLen \in Nat /\ MaxLen >= 1
ASSUME ValuesAssump == Values \subseteq Int /\ IsFiniteSet(Values) /\ Values # {}

NotFound == 0

(***************************************************************************)
(* Input domain                                                            *)
(***************************************************************************)
BoundedSeqs == UNION { [1..n -> Values] : n \in 1..MaxLen }

IsSorted(s) == \A i, j \in 1..Len(s) : i <= j => s[i] <= s[j]

SortedSeqs == { s \in BoundedSeqs : IsSorted(s) }

Range(s) == { s[i] : i \in 1..Len(s) }

VARIABLES
    seq,        \* the input sequence (fixed after Init)
    target,     \* the key being searched for (fixed after Init)
    lo,         \* lower bound of the current search interval
    hi,         \* upper bound of the current search interval
    result,     \* NotFound or an index into seq
    pc          \* "search" or "done"

vars == << seq, target, lo, hi, result, pc >>

Mid == (lo + hi) \div 2

(***************************************************************************)
(* Initial conditions                                                      *)
(***************************************************************************)
Init ==
    /\ seq    \in SortedSeqs
    /\ target \in Values
    /\ lo     = 1
    /\ hi     = Len(seq)
    /\ result = NotFound
    /\ pc     = "search"

(***************************************************************************)
(* Transitions                                                             *)
(***************************************************************************)
\* Empty interval: the target is absent; report failure deterministically.
Fail ==
    /\ pc = "search"
    /\ lo > hi
    /\ result' = NotFound
    /\ pc'     = "done"
    /\ UNCHANGED << seq, target, lo, hi >>

\* Probe the middle element and either finish or shrink the interval.
Probe ==
    /\ pc = "search"
    /\ lo <= hi
    /\ CASE seq[Mid] = target ->
                /\ result' = Mid
                /\ pc'     = "done"
                /\ UNCHANGED << lo, hi >>
         [] seq[Mid] < target ->
                /\ lo' = Mid + 1
                /\ UNCHANGED << hi, result, pc >>
         [] seq[Mid] > target ->
                /\ hi' = Mid - 1
                /\ UNCHANGED << lo, result, pc >>
    /\ UNCHANGED << seq, target >>

Step == Fail \/ Probe

\* Termination: once done, the system only stutters (avoids deadlock reports).
Terminated ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == Step \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

(***************************************************************************)
(* Type invariant                                                          *)
(***************************************************************************)
TypeOK ==
    /\ seq \in SortedSeqs
    /\ target \in Values
    /\ lo \in 1..(Len(seq) + 1)
    /\ hi \in 0..Len(seq)
    /\ result \in {NotFound} \cup (1..Len(seq))
    /\ pc \in {"search", "done"}

(***************************************************************************)
(* Key invariants                                                          *)
(***************************************************************************)
\* The input never changes during the search.
InputSorted == IsSorted(seq) /\ Len(seq) \in 1..MaxLen

\* Interval bounds remain within sequence limits.
BoundsInv ==
    /\ 1 <= lo /\ lo <= Len(seq) + 1
    /\ 0 <= hi /\ hi <= Len(seq)
    /\ lo <= hi + 1

\* If the target is present, it lies within the current search interval.
TargetInInterval ==
    (pc = "search" /\ target \in Range(seq))
        => \E i \in lo..hi : seq[i] = target

\* Every element strictly outside the interval differs from the target
\* (stronger form, valid with duplicates).
OutsideExcluded ==
    pc = "search" =>
        /\ \A i \in 1..(lo - 1)       : seq[i] < target
        /\ \A i \in (hi + 1)..Len(seq) : seq[i] > target

(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)
\* No out-of-bounds access: whenever a probe can occur, Mid is a valid index.
NoOutOfBounds ==
    (pc = "search" /\ lo <= hi) => Mid \in 1..Len(seq)

\* Only valid indices are ever returned, and they point to the target.
ValidResult ==
    result # NotFound =>
        /\ result \in 1..Len(seq)
        /\ seq[result] = target

\* Correctness of the final result: found iff membership.
Correctness ==
    pc = "done" =>
        /\ (result # NotFound) <=> (target \in Range(seq))
        /\ (result # NotFound) => seq[result] = target

\* Deterministic failure: if absent, the result is always NotFound.
DeterministicFailure ==
    (pc = "done" /\ target \notin Range(seq)) => result = NotFound

SafetyInv ==
    /\ TypeOK
    /\ InputSorted
    /\ BoundsInv
    /\ TargetInInterval
    /\ OutsideExcluded
    /\ NoOutOfBounds
    /\ ValidResult
    /\ Correctness
    /\ DeterministicFailure

(***************************************************************************)
(* Progress / variant: the interval strictly decreases until termination.  *)
(***************************************************************************)
IntervalSize == hi - lo + 1

IntervalStrictlyDecreases ==
    [][ (pc = "search" /\ pc' = "search") => IntervalSize' < IntervalSize ]_vars

InputConstant ==
    [][ seq' = seq /\ target' = target ]_vars

DoneIsFinal ==
    [][ pc = "done" => UNCHANGED vars ]_vars

(***************************************************************************)
(* Liveness: eventual termination on all inputs within the bounded size.   *)
(***************************************************************************)
Termination == <>(pc = "done")

EventuallyCorrect == <>(pc = "done" /\ Correctness)

THEOREM Spec => []SafetyInv
THEOREM Spec => IntervalStrictlyDecreases /\ InputConstant /\ DoneIsFinal
THEOREM Spec => Termination /\ EventuallyCorrect
================================================================================