---------------------------- MODULE MergeSort ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS ArrayLen, defaultInitValue

VARIABLES a, b, pc, stack, lo, hi, mid

vars == <<a, b, pc, stack, lo, hi, mid>>

N == ArrayLen

Values == 1..N

Arrays == [1..N -> Values]

Init ==
    /\ a \in UNION {[1..len -> Values] : len \in 1..ArrayLen}
    /\ b = [i \in 1..ArrayLen |-> defaultInitValue]
    /\ pc = "MergeSort"
    /\ stack = <<>>
    /\ lo = 1
    /\ hi = Len(a)
    /\ mid = defaultInitValue

Sorted(arr) ==
    \A i \in 1..(Len(arr)-1) : arr[i] <= arr[i+1]

Merge(arr, buf, l, m, h) ==
    LET left == SubSeq(arr, l, m)
        right == SubSeq(arr, m+1, h)
        MergeSeqs[ll \in 0..Len(left), rr \in 0..Len(right)] ==
            IF ll = 0 /\ rr = 0 THEN <<>>
            ELSE IF ll = 0 THEN <<right[rr]>> \o MergeSeqs[0, rr-1]
            ELSE IF rr = 0 THEN <<left[ll]>> \o MergeSeqs[ll-1, 0]
            ELSE IF left[Len(left)-ll+1] <= right[Len(right)-rr+1]
                 THEN <<left[Len(left)-ll+1]>> \o MergeSeqs[ll-1, rr]
                 ELSE <<right[Len(right)-rr+1]>> \o MergeSeqs[ll, rr-1]
        merged == MergeSeqs[Len(left), Len(right)]
    IN [i \in 1..Len(arr) |-> IF i >= l /\ i <= h THEN merged[i-l+1] ELSE arr[i]]

MergeSortStart ==
    /\ pc = "MergeSort"
    /\ IF lo < hi
       THEN /\ mid' = (lo + hi) \div 2
            /\ stack' = <<[proc |-> "MergeSort", lo |-> lo, hi |-> hi, mid |-> mid', ret |-> "LeftDone"]>> \o stack
            /\ hi' = mid'
            /\ pc' = "MergeSort"
            /\ UNCHANGED <<a, b, lo>>
       ELSE /\ pc' = "Return"
            /\ UNCHANGED <<a, b, stack, lo, hi, mid>>

LeftDone ==
    /\ pc = "LeftDone"
    /\ LET frame == Head(stack)
       IN /\ lo' = frame.mid + 1
          /\ hi' = frame.hi
          /\ mid' = frame.mid
          /\ stack' = <<[proc |-> "Merge", lo |-> frame.lo, hi |-> frame.hi, mid |-> frame.mid, ret |-> "MergeDone"]>> \o Tail(stack)
          /\ pc' = "MergeSort"
    /\ UNCHANGED <<a, b>>

MergeDone ==
    /\ pc = "MergeDone"
    /\ LET frame == Head(stack)
       IN /\ a' = Merge(a, b, frame.lo, frame.mid, frame.hi)
          /\ stack' = Tail(stack)
          /\ pc' = "Return"
    /\ UNCHANGED <<b, lo, hi, mid>>

Return ==
    /\ pc = "Return"
    /\ IF stack = <<>>
       THEN /\ pc' = "Done"
            /\ UNCHANGED <<a, b, stack, lo, hi, mid>>
       ELSE LET frame == Head(stack)
            IN /\ pc' = frame.ret
               /\ lo' = frame.lo
               /\ hi' = frame.hi
               /\ mid' = frame.mid
               /\ stack' = Tail(stack)
               /\ UNCHANGED <<a, b>>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ MergeSortStart
    \/ LeftDone
    \/ MergeDone
    \/ Return
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

Invariant == pc = "Done" => Sorted(a)

=============================================================================