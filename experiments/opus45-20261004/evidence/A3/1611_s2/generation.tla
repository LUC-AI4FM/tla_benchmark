---------------------------- MODULE MergeSort ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS ArrayLen, N

ASSUME ArrayLen \in Nat /\ ArrayLen >= 0
ASSUME N \in Nat /\ N >= 1

VARIABLES a, b, pc, stack, lo, hi, mid

vars == <<a, b, pc, stack, lo, hi, mid>>

\* Helper function to check if array segment is sorted
IsSorted(arr, l, h) ==
    \A i, j \in l..h : i <= j => arr[i] <= arr[j]

\* Helper function to check if entire array is sorted
ArrayIsSorted ==
    \A i, j \in DOMAIN a : i <= j => a[i] <= a[j]

\* All possible arrays of length len with values in 1..N
Arrays(len) ==
    [1..len -> 1..N]

\* All possible arrays up to length ArrayLen
AllArrays ==
    UNION {Arrays(len) : len \in 0..ArrayLen}

TypeOK ==
    /\ a \in AllArrays
    /\ b \in AllArrays
    /\ pc \in {"start", "sort", "split", "merge", "mergeLoop", "copyBack", "return", "Done"}
    /\ stack \in Seq([lo : Nat, hi : Nat, mid : Nat, retpc : {"split", "merge", "return"}])
    /\ lo \in Nat
    /\ hi \in Nat
    /\ mid \in Nat

Init ==
    /\ a \in AllArrays
    /\ b = [i \in DOMAIN a |-> 0]
    /\ pc = "start"
    /\ stack = <<>>
    /\ lo = 1
    /\ hi = 0
    /\ mid = 0

\* Start the sort on the entire array
Start ==
    /\ pc = "start"
    /\ IF Len(a) > 0
       THEN /\ lo' = 1
            /\ hi' = Len(a)
            /\ pc' = "sort"
       ELSE /\ pc' = "Done"
            /\ lo' = lo
            /\ hi' = hi
    /\ UNCHANGED <<a, b, stack, mid>>

\* Main sort procedure entry point
Sort ==
    /\ pc = "sort"
    /\ IF hi <= lo
       THEN \* Base case: segment of length 0 or 1, already sorted
            /\ pc' = "return"
            /\ UNCHANGED <<a, b, stack, lo, hi, mid>>
       ELSE \* Recursive case: split and sort both halves
            /\ mid' = (lo + hi) \div 2
            /\ stack' = Append(stack, [lo |-> lo, hi |-> hi, mid |-> (lo + hi) \div 2, retpc |-> "split"])
            /\ hi' = (lo + hi) \div 2
            /\ pc' = "sort"
            /\ UNCHANGED <<a, b, lo>>

\* After sorting left half, sort right half
Split ==
    /\ pc = "split"
    /\ Len(stack) > 0
    /\ LET frame == stack[Len(stack)]
       IN /\ stack' = Append(SubSeq(stack, 1, Len(stack) - 1), 
                             [lo |-> frame.lo, hi |-> frame.hi, mid |-> frame.mid, retpc |-> "merge"])
          /\ lo' = frame.mid + 1
          /\ hi' = frame.hi
          /\ mid' = frame.mid
          /\ pc' = "sort"
    /\ UNCHANGED <<a, b>>

\* After sorting both halves, merge them
Merge ==
    /\ pc = "merge"
    /\ Len(stack) > 0
    /\ LET frame == stack[Len(stack)]
       IN /\ lo' = frame.lo
          /\ hi' = frame.hi
          /\ mid' = frame.mid
          /\ pc' = "mergeLoop"
          /\ stack' = SubSeq(stack, 1, Len(stack) - 1)
    /\ UNCHANGED <<a, b>>

\* Perform the merge of two sorted halves into buffer b
MergeLoop ==
    /\ pc = "mergeLoop"
    /\ LET leftStart == lo
           leftEnd == mid
           rightStart == mid + 1
           rightEnd == hi
       IN /\ b' = [i \in DOMAIN a |->
                    IF i < lo \/ i > hi
                    THEN b[i]
                    ELSE LET MergeHelper[left \in lo..(mid+1), right \in (mid+1)..(hi+1), pos \in lo..(hi+1)] ==
                             IF pos > hi
                             THEN <<>>
                             ELSE IF left > mid
                                  THEN <<a[right]>> \o MergeHelper[left, right + 1, pos + 1]
                                  ELSE IF right > hi
                                       THEN <<a[left]>> \o MergeHelper[left + 1, right, pos + 1]
                                       ELSE IF a[left] <= a[right]
                                            THEN <<a[left]>> \o MergeHelper[left + 1, right, pos + 1]
                                            ELSE <<a[right]>> \o MergeHelper[left, right + 1, pos + 1]
                             IN LET merged == MergeHelper[lo, mid + 1, lo]
                                IN IF i - lo + 1 <= Len(merged)
                                   THEN merged[i - lo + 1]
                                   ELSE b[i]]
          /\ pc' = "copyBack"
    /\ UNCHANGED <<a, stack, lo, hi, mid>>

\* Copy merged result back from b to a
CopyBack ==
    /\ pc = "copyBack"
    /\ a' = [i \in DOMAIN a |->
              IF i >= lo /\ i <= hi
              THEN b[i]
              ELSE a[i]]
    /\ pc' = "return"
    /\ UNCHANGED <<b, stack, lo, hi, mid>>

\* Return from recursive call
Return ==
    /\ pc = "return"
    /\ IF Len(stack) = 0
       THEN /\ pc' = "Done"
            /\ UNCHANGED <<a, b, stack, lo, hi, mid>>
       ELSE LET frame == stack[Len(stack)]
            IN /\ pc' = frame.retpc
               /\ UNCHANGED <<a, b, stack, lo, hi, mid>>

\* Terminal state
Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Start
    \/ Sort
    \/ Split
    \/ Merge
    \/ MergeLoop
    \/ CopyBack
    \/ Return
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Safety property: when done, array is sorted
Sorted == pc = "Done" => ArrayIsSorted

\* Termination property
Termination == <>(pc = "Done")

==========================================================================