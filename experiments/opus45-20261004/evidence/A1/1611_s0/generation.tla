---------------------------- MODULE mergesort ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS ArrayLen, defaultInitValue

VARIABLES a, b, pc, stack, lo, hi, mid

vars == <<a, b, pc, stack, lo, hi, mid>>

\* Helper function to check if array segment is sorted
IsSorted(arr, from, to) ==
    \A i, j \in from..to : i <= j => arr[i] <= arr[j]

\* Helper function to check if entire array is sorted
ArrayIsSorted ==
    \A i, j \in 1..Len(a) : i <= j => a[i] <= a[j]

\* Generate all possible arrays of length len with values in 1..ArrayLen
PossibleArrays(len) ==
    [1..len -> 1..ArrayLen]

\* All possible initial arrays (lengths 0 to ArrayLen)
AllArrays ==
    UNION {PossibleArrays(len) : len \in 1..ArrayLen} \cup {<<>>}

Init ==
    /\ a \in AllArrays
    /\ b = [i \in 1..ArrayLen |-> defaultInitValue]
    /\ pc = "mergesort"
    /\ stack = <<>>
    /\ lo = 1
    /\ hi = Len(a)
    /\ mid = defaultInitValue

\* Merge procedure: merge a[lo..mid] and a[mid+1..hi] using buffer b
Merge(loVal, midVal, hiVal) ==
    LET leftPart == SubSeq(a, loVal, midVal)
        rightPart == SubSeq(a, midVal + 1, hiVal)
        MergeSeqs[l \in Seq(1..ArrayLen), r \in Seq(1..ArrayLen)] ==
            IF l = <<>> THEN r
            ELSE IF r = <<>> THEN l
            ELSE IF Head(l) <= Head(r) 
                 THEN <<Head(l)>> \o MergeSeqs[Tail(l), r]
                 ELSE <<Head(r)>> \o MergeSeqs[l, Tail(r)]
        merged == MergeSeqs[leftPart, rightPart]
        newA == [i \in 1..Len(a) |-> 
                    IF i >= loVal /\ i <= hiVal 
                    THEN merged[i - loVal + 1]
                    ELSE a[i]]
    IN newA

\* MergeSort procedure start
MergeSortStart ==
    /\ pc = "mergesort"
    /\ IF lo >= hi
       THEN \* Base case: already sorted
            /\ IF stack = <<>>
               THEN pc' = "Done"
               ELSE 
                    /\ pc' = stack[1].pc
                    /\ lo' = stack[1].lo
                    /\ hi' = stack[1].hi
                    /\ mid' = stack[1].mid
                    /\ stack' = Tail(stack)
            /\ UNCHANGED <<a, b>>
       ELSE \* Recursive case: compute mid and recurse on left half
            /\ mid' = (lo + hi) \div 2
            /\ stack' = <<[pc |-> "ms_after_left", lo |-> lo, hi |-> hi, mid |-> (lo + hi) \div 2]>> \o stack
            /\ hi' = (lo + hi) \div 2
            /\ pc' = "mergesort"
            /\ UNCHANGED <<a, b, lo>>

\* After returning from left recursive call
AfterLeftCall ==
    /\ pc = "ms_after_left"
    /\ stack' = <<[pc |-> "ms_after_right", lo |-> lo, hi |-> hi, mid |-> mid]>> \o stack
    /\ lo' = mid + 1
    /\ pc' = "mergesort"
    /\ UNCHANGED <<a, b, hi, mid>>

\* After returning from right recursive call
AfterRightCall ==
    /\ pc = "ms_after_right"
    /\ a' = Merge(lo, mid, hi)
    /\ IF Tail(stack) = <<>>
       THEN 
            /\ pc' = "Done"
            /\ stack' = <<>>
            /\ lo' = lo
            /\ hi' = hi
            /\ mid' = mid
       ELSE
            /\ pc' = Tail(stack)[1].pc
            /\ lo' = Tail(stack)[1].lo
            /\ hi' = Tail(stack)[1].hi
            /\ mid' = Tail(stack)[1].mid
            /\ stack' = Tail(Tail(stack))
    /\ UNCHANGED b

Terminated ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ MergeSortStart
    \/ AfterLeftCall
    \/ AfterRightCall
    \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* Safety invariant: when done, array is sorted
Invariant ==
    pc = "Done" => (Len(a) <= 1 \/ ArrayIsSorted)

==========================================================================