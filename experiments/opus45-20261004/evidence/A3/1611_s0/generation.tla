---------------------------- MODULE MergeSort ----------------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS ArrayLen, N

ASSUME ArrayLen \in Nat /\ ArrayLen >= 0
ASSUME N \in Nat /\ N >= 1

VARIABLES a, b, pc, stack

vars == <<a, b, pc, stack>>

\* Helper function to check if array segment is sorted
IsSorted(arr, lo, hi) ==
    \A i, j \in lo..hi : i < j => arr[i] <= arr[j]

\* Helper function to check if entire array is sorted
ArraySorted ==
    IF Len(a) = 0 THEN TRUE
    ELSE IsSorted(a, 1, Len(a))

\* All possible arrays of length len with values in 1..N
Arrays(len) ==
    [1..len -> 1..N]

\* All possible initial arrays (all lengths from 0 to ArrayLen)
AllArrays ==
    UNION {Arrays(len) : len \in 0..ArrayLen}

\* Stack frame for recursive calls
\* Each frame contains: lo, hi, mid, returnLabel
StackFrame == [lo : Nat, hi : Nat, mid : Nat, retLabel : {"merge", "return"}]

Init ==
    /\ a \in AllArrays
    /\ b = [i \in 1..Len(a) |-> 0]
    /\ pc = IF Len(a) <= 1 THEN "Done" ELSE "sort"
    /\ stack = IF Len(a) <= 1 THEN <<>> 
               ELSE <<[lo |-> 1, hi |-> Len(a), mid |-> 0, retLabel |-> "return"]>>

\* Sort: Initial entry point for sorting segment [lo, hi]
Sort ==
    /\ pc = "sort"
    /\ stack # <<>>
    /\ LET frame == Head(stack)
           lo == frame.lo
           hi == frame.hi
       IN
       IF hi - lo < 1
       THEN \* Base case: segment of size 0 or 1, already sorted
            /\ IF frame.retLabel = "return"
               THEN /\ stack' = Tail(stack)
                    /\ pc' = IF Tail(stack) = <<>> THEN "Done" ELSE "continue"
               ELSE /\ stack' = Tail(stack)
                    /\ pc' = "merge"
            /\ UNCHANGED <<a, b>>
       ELSE \* Recursive case: split and sort left half first
            LET mid == (lo + hi) \div 2
                newFrame == [lo |-> lo, hi |-> mid, mid |-> 0, retLabel |-> "merge"]
                updatedCurrent == [frame EXCEPT !.mid = mid]
            IN
            /\ stack' = <<newFrame, updatedCurrent>> \o Tail(stack)
            /\ pc' = "sort"
            /\ UNCHANGED <<a, b>>

\* Continue: Process return from recursive call
Continue ==
    /\ pc = "continue"
    /\ stack # <<>>
    /\ LET frame == Head(stack)
       IN
       IF frame.retLabel = "merge"
       THEN \* After left half sorted, now sort right half
            LET mid == frame.mid
                lo == frame.lo
                hi == frame.hi
                newFrame == [lo |-> mid + 1, hi |-> hi, mid |-> 0, retLabel |-> "merge"]
                updatedCurrent == [frame EXCEPT !.retLabel = "return"]
            IN
            /\ stack' = <<newFrame, updatedCurrent>> \o Tail(stack)
            /\ pc' = "sort"
            /\ UNCHANGED <<a, b>>
       ELSE \* retLabel = "return", pop and continue
            /\ stack' = Tail(stack)
            /\ pc' = IF Tail(stack) = <<>> THEN "Done" ELSE "continue"
            /\ UNCHANGED <<a, b>>

\* Merge: Merge two sorted halves
Merge ==
    /\ pc = "merge"
    /\ stack # <<>>
    /\ LET frame == Head(stack)
           lo == frame.lo
           hi == frame.hi
           mid == frame.mid
       IN
       \* Copy to buffer
       LET b1 == [i \in 1..Len(a) |-> IF i >= lo /\ i <= hi THEN a[i] ELSE b[i]]
       IN
       \* Merge back to a
       LET MergeLoop(aInit, left, right, k) ==
               LET RECURSIVE DoMerge(_, _, _, _)
                   DoMerge(arr, l, r, idx) ==
                       IF idx > hi THEN arr
                       ELSE IF l > mid THEN 
                                DoMerge([arr EXCEPT ![idx] = b1[r]], l, r+1, idx+1)
                            ELSE IF r > hi THEN
                                DoMerge([arr EXCEPT ![idx] = b1[l]], l+1, r, idx+1)
                            ELSE IF b1[l] <= b1[r] THEN
                                DoMerge([arr EXCEPT ![idx] = b1[l]], l+1, r, idx+1)
                            ELSE
                                DoMerge([arr EXCEPT ![idx] = b1[r]], l, r+1, idx+1)
               IN DoMerge(aInit, left, right, k)
           a1 == MergeLoop(a, lo, mid+1, lo)
       IN
       /\ a' = a1
       /\ b' = b1
       /\ IF frame.retLabel = "return"
          THEN /\ stack' = Tail(stack)
               /\ pc' = IF Tail(stack) = <<>> THEN "Done" ELSE "continue"
          ELSE /\ stack' = Tail(stack)
               /\ pc' = "continue"

Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Sort
    \/ Continue
    \/ Merge
    \/ Done

Fairness == WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety invariant: When done, array is sorted
SafetyInvariant ==
    pc = "Done" => ArraySorted

\* Type invariant
TypeInvariant ==
    /\ a \in [1..Len(a) -> 1..N] \/ a = <<>>
    /\ b \in [1..Len(b) -> 0..N] \/ b = <<>>
    /\ Len(a) = Len(b)
    /\ pc \in {"sort", "continue", "merge", "Done"}

\* Termination property
Termination == <>(pc = "Done")

==========================================================================