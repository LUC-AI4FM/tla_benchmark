---------------------------- MODULE MergeSort ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS ArrayLen, N

ASSUME ArrayLen \in Nat /\ ArrayLen >= 0
ASSUME N \in Nat /\ N >= 1

VARIABLES a, b, stack, pc

vars == <<a, b, stack, pc>>

\* Helper: sequence of integers from m to n
SeqFromTo(m, n) == [i \in 1..(n - m + 1) |-> m + i - 1]

\* Check if array a is sorted from index lo to hi
IsSorted(arr, lo, hi) == \A i \in lo..(hi-1) : arr[i] <= arr[i+1]

\* Check if entire array is sorted
Sorted == IF Len(a) = 0 THEN TRUE ELSE IsSorted(a, 1, Len(a))

\* Stack frame: <<lo, hi, phase>>
\* phase = "call" means we need to process this range
\* phase = "merge" means we need to merge after recursive calls returned

Init ==
    /\ a \in [1..ArrayLen -> 1..N] \cup {<<>>}
    /\ b = [i \in 1..ArrayLen |-> 0]
    /\ stack = IF Len(a) <= 1 
               THEN <<>> 
               ELSE <<<<1, Len(a), "call">>>>
    /\ pc = IF Len(a) <= 1 THEN "Done" ELSE "Run"

\* Merge subroutine: merge a[lo..mid] and a[mid+1..hi] into a[lo..hi]
Merge(arr, buf, lo, mid, hi) ==
    LET left == SubSeq(arr, lo, mid)
        right == SubSeq(arr, mid + 1, hi)
        MergeSeqs[p \in 0..(hi - lo + 1)] ==
            IF p = 0 THEN <<>>
            ELSE LET i == Len([q \in 1..p |-> 
                              IF \E j \in 1..Len(MergeSeqs[p-1]) : 
                                 MergeSeqs[p-1][j] = left[q] 
                              THEN 0 ELSE 1])
                 IN <<>>
    IN LET 
        MergeHelper[state \in SUBSET (1..(hi - lo + 1))] ==
            <<>>
        DoMerge == 
            LET len == hi - lo + 1
                Result[k \in 0..len] ==
                    IF k = 0 THEN <<[], 1, 1>>
                    ELSE LET prev == Result[k-1]
                             merged == prev[1]
                             li == prev[2]
                             ri == prev[3]
                         IN IF li > Len(left) THEN 
                                <<Append(merged, right[ri]), li, ri + 1>>
                            ELSE IF ri > Len(right) THEN
                                <<Append(merged, left[li]), li + 1, ri>>
                            ELSE IF left[li] <= right[ri] THEN
                                <<Append(merged, left[li]), li + 1, ri>>
                            ELSE
                                <<Append(merged, right[ri]), li, ri + 1>>
            IN Result[len][1]
        merged == DoMerge
        newArr == [i \in 1..Len(arr) |-> 
                   IF i >= lo /\ i <= hi 
                   THEN merged[i - lo + 1]
                   ELSE arr[i]]
    IN newArr

\* Process a call frame
ProcessCall(lo, hi) ==
    IF hi <= lo 
    THEN \* Base case: single element or empty, pop and continue
         /\ stack' = Tail(stack)
         /\ UNCHANGED <<a, b>>
    ELSE \* Recursive case: push merge frame, then two call frames
         LET mid == (lo + hi) \div 2
         IN /\ stack' = <<<<lo, hi, "merge">>, 
                          <<mid + 1, hi, "call">>,
                          <<lo, mid, "call">>> \o Tail(stack)
            /\ UNCHANGED <<a, b>>

\* Process a merge frame
ProcessMerge(lo, hi) ==
    LET mid == (lo + hi) \div 2
    IN /\ a' = Merge(a, b, lo, mid, hi)
       /\ stack' = Tail(stack)
       /\ UNCHANGED b

Step ==
    /\ pc = "Run"
    /\ stack /= <<>>
    /\ LET frame == Head(stack)
           lo == frame[1]
           hi == frame[2]
           phase == frame[3]
       IN IF phase = "call" 
          THEN ProcessCall(lo, hi)
          ELSE ProcessMerge(lo, hi)
    /\ pc' = IF Tail(stack') = <<>> /\ stack' = <<>> THEN "Done" 
             ELSE IF stack' = <<>> THEN "Done" ELSE "Run"

\* Corrected step that properly updates pc
Next ==
    \/ /\ pc = "Run"
       /\ stack /= <<>>
       /\ LET frame == Head(stack)
              lo == frame[1]
              hi == frame[2]
              phase == frame[3]
          IN IF phase = "call"
             THEN IF hi <= lo
                  THEN /\ stack' = Tail(stack)
                       /\ UNCHANGED <<a, b>>
                  ELSE LET mid == (lo + hi) \div 2
                       IN /\ stack' = <<<<lo, hi, "merge">>, 
                                        <<mid + 1, hi, "call">>,
                                        <<lo, mid, "call">>> \o Tail(stack)
                          /\ UNCHANGED <<a, b>>
             ELSE LET mid == (lo + hi) \div 2
                  IN /\ a' = Merge(a, b, lo, mid, hi)
                     /\ stack' = Tail(stack)
                     /\ UNCHANGED b
       /\ pc' = IF stack' = <<>> THEN "Done" ELSE "Run"
    \/ /\ pc = "Done"
       /\ UNCHANGED vars

TypeOK ==
    /\ a \in [1..Len(a) -> 1..N] \cup {<<>>}
    /\ pc \in {"Run", "Done"}

\* Safety: when done, array is sorted
SafetyInvariant ==
    pc = "Done" => Sorted

\* Termination: eventually we reach Done
Termination == <>(pc = "Done")

Fairness == WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

=========================================================================