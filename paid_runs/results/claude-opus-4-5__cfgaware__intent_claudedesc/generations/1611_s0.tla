---------------------------- MODULE MergeSort ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT ArrayLen

ASSUME ArrayLen \in Nat

defaultInitValue == CHOOSE v : v \notin (0..ArrayLen)

VARIABLES A, B, pc, stack, lo, hi, m, i, j, k

vars == <<A, B, pc, stack, lo, hi, m, i, j, k>>

Init ==
    /\ A \in [1..ArrayLen -> 0..ArrayLen] \cup {<<>>}
    /\ B = [x \in 1..ArrayLen |-> defaultInitValue]
    /\ pc = "Start"
    /\ stack = <<>>
    /\ lo = defaultInitValue
    /\ hi = defaultInitValue
    /\ m = defaultInitValue
    /\ i = defaultInitValue
    /\ j = defaultInitValue
    /\ k = defaultInitValue

Start ==
    /\ pc = "Start"
    /\ IF Len(A) > 0
       THEN /\ stack' = <<[proc |-> "sort", lo |-> 1, hi |-> Len(A), m |-> defaultInitValue, 
                           i |-> defaultInitValue, j |-> defaultInitValue, k |-> defaultInitValue]>> \o stack
            /\ lo' = 1
            /\ hi' = Len(A)
            /\ m' = defaultInitValue
            /\ i' = defaultInitValue
            /\ j' = defaultInitValue
            /\ k' = defaultInitValue
            /\ pc' = "SortCheck"
       ELSE /\ pc' = "Done"
            /\ UNCHANGED <<stack, lo, hi, m, i, j, k>>
    /\ UNCHANGED <<A, B>>

SortCheck ==
    /\ pc = "SortCheck"
    /\ IF hi > lo
       THEN /\ m' = lo + ((hi - lo) \div 2)
            /\ pc' = "SortLeft"
       ELSE /\ pc' = "SortReturn"
            /\ m' = m
    /\ UNCHANGED <<A, B, stack, lo, hi, i, j, k>>

SortLeft ==
    /\ pc = "SortLeft"
    /\ stack' = <<[proc |-> "sort", lo |-> lo, hi |-> hi, m |-> m,
                   i |-> i, j |-> j, k |-> k]>> \o stack
    /\ lo' = lo
    /\ hi' = m
    /\ m' = defaultInitValue
    /\ i' = defaultInitValue
    /\ j' = defaultInitValue
    /\ k' = defaultInitValue
    /\ pc' = "SortCheck"
    /\ UNCHANGED <<A, B>>

SortRight ==
    /\ pc = "SortRight"
    /\ stack' = <<[proc |-> "sort", lo |-> lo, hi |-> hi, m |-> m,
                   i |-> i, j |-> j, k |-> k]>> \o stack
    /\ lo' = m + 1
    /\ hi' = hi
    /\ m' = defaultInitValue
    /\ i' = defaultInitValue
    /\ j' = defaultInitValue
    /\ k' = defaultInitValue
    /\ pc' = "SortCheck"
    /\ UNCHANGED <<A, B>>

SortMerge ==
    /\ pc = "SortMerge"
    /\ pc' = "MergeCopyLeft"
    /\ i' = lo
    /\ UNCHANGED <<A, B, stack, lo, hi, m, j, k>>

MergeCopyLeft ==
    /\ pc = "MergeCopyLeft"
    /\ IF i <= m
       THEN /\ B' = [B EXCEPT ![i] = A[i]]
            /\ i' = i + 1
            /\ pc' = "MergeCopyLeft"
       ELSE /\ j' = m + 1
            /\ pc' = "MergeCopyRight"
            /\ i' = i
            /\ B' = B
    /\ UNCHANGED <<A, stack, lo, hi, m, k>>

MergeCopyRight ==
    /\ pc = "MergeCopyRight"
    /\ IF j <= hi
       THEN /\ B' = [B EXCEPT ![hi + m + 1 - j] = A[j]]
            /\ j' = j + 1
            /\ pc' = "MergeCopyRight"
       ELSE /\ i' = lo
            /\ j' = hi
            /\ k' = lo
            /\ pc' = "MergeLoop"
            /\ B' = B
    /\ UNCHANGED <<A, stack, lo, hi, m>>

MergeLoop ==
    /\ pc = "MergeLoop"
    /\ IF k <= hi
       THEN /\ IF B[i] <= B[j]
               THEN /\ A' = [A EXCEPT ![k] = B[i]]
                    /\ i' = i + 1
                    /\ j' = j
               ELSE /\ A' = [A EXCEPT ![k] = B[j]]
                    /\ j' = j - 1
                    /\ i' = i
            /\ k' = k + 1
            /\ pc' = "MergeLoop"
       ELSE /\ pc' = "SortReturn"
            /\ UNCHANGED <<A, i, j, k>>
    /\ UNCHANGED <<B, stack, lo, hi, m>>

SortReturn ==
    /\ pc = "SortReturn"
    /\ IF Len(stack) > 0
       THEN /\ LET frame == Head(stack) IN
                 /\ lo' = frame.lo
                 /\ hi' = frame.hi
                 /\ m' = frame.m
                 /\ i' = frame.i
                 /\ j' = frame.j
                 /\ k' = frame.k
                 /\ stack' = Tail(stack)
                 /\ IF frame.m # defaultInitValue /\ frame.i = defaultInitValue
                    THEN pc' = "SortRight"
                    ELSE IF frame.m # defaultInitValue /\ frame.i # defaultInitValue /\ frame.k = defaultInitValue
                         THEN pc' = "SortMerge"
                         ELSE pc' = "SortReturn"
       ELSE /\ pc' = "Done"
            /\ UNCHANGED <<stack, lo, hi, m, i, j, k>>
    /\ UNCHANGED <<A, B>>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Start
    \/ SortCheck
    \/ SortLeft
    \/ SortRight
    \/ SortMerge
    \/ MergeCopyLeft
    \/ MergeCopyRight
    \/ MergeLoop
    \/ SortReturn
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

IsSorted == \A x, y \in DOMAIN A : x < y => A[x] <= A[y]

Termination == <>(pc = "Done")

Invariant == pc = "Done" => IsSorted

==========================================================================