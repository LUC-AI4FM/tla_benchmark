---------------------------- MODULE MergeSort ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT ArrayLen

VARIABLES a, b, N, pc, stack, l, r, i, j, k, m

vars == <<a, b, N, pc, stack, l, r, i, j, k, m>>

Init ==
    /\ N \in 0..ArrayLen
    /\ a \in [1..N -> 1..N]
    /\ b = [x \in 1..N |-> 0]
    /\ pc = "main"
    /\ stack = <<>>
    /\ l = 1
    /\ r = N
    /\ i = 0
    /\ j = 0
    /\ k = 0
    /\ m = 0

CallMergeSort(larg, rarg) ==
    /\ stack' = <<[pc |-> pc, l |-> l, r |-> r, i |-> i, j |-> j, k |-> k, m |-> m]>> \o stack
    /\ l' = larg
    /\ r' = rarg
    /\ i' = 0
    /\ j' = 0
    /\ k' = 0
    /\ m' = 0
    /\ pc' = "ms_start"

Return ==
    /\ stack # <<>>
    /\ pc' = Head(stack).pc
    /\ l' = Head(stack).l
    /\ r' = Head(stack).r
    /\ i' = Head(stack).i
    /\ j' = Head(stack).j
    /\ k' = Head(stack).k
    /\ m' = Head(stack).m
    /\ stack' = Tail(stack)

Main ==
    /\ pc = "main"
    /\ IF N > 0
       THEN CallMergeSort(1, N) /\ UNCHANGED <<a, b, N>>
       ELSE /\ pc' = "Done"
            /\ UNCHANGED <<a, b, N, stack, l, r, i, j, k, m>>

MsStart ==
    /\ pc = "ms_start"
    /\ IF l < r
       THEN /\ m' = (l + r) \div 2
            /\ pc' = "ms_left"
            /\ UNCHANGED <<a, b, N, stack, l, r, i, j, k>>
       ELSE /\ pc' = "ms_return"
            /\ UNCHANGED <<a, b, N, stack, l, r, i, j, k, m>>

MsLeft ==
    /\ pc = "ms_left"
    /\ stack' = <<[pc |-> "ms_right", l |-> l, r |-> r, i |-> i, j |-> j, k |-> k, m |-> m]>> \o stack
    /\ r' = m
    /\ i' = 0
    /\ j' = 0
    /\ k' = 0
    /\ pc' = "ms_start"
    /\ UNCHANGED <<a, b, N, l, m>>

MsRight ==
    /\ pc = "ms_right"
    /\ stack' = <<[pc |-> "ms_copy_left_init", l |-> l, r |-> r, i |-> i, j |-> j, k |-> k, m |-> m]>> \o stack
    /\ l' = m + 1
    /\ i' = 0
    /\ j' = 0
    /\ k' = 0
    /\ pc' = "ms_start"
    /\ UNCHANGED <<a, b, N, r, m>>

MsCopyLeftInit ==
    /\ pc = "ms_copy_left_init"
    /\ i' = l
    /\ pc' = "ms_copy_left"
    /\ UNCHANGED <<a, b, N, stack, l, r, j, k, m>>

MsCopyLeft ==
    /\ pc = "ms_copy_left"
    /\ IF i <= m
       THEN /\ b' = [b EXCEPT ![i] = a[i]]
            /\ i' = i + 1
            /\ pc' = "ms_copy_left"
            /\ UNCHANGED <<a, N, stack, l, r, j, k, m>>
       ELSE /\ pc' = "ms_copy_right_init"
            /\ UNCHANGED <<a, b, N, stack, l, r, i, j, k, m>>

MsCopyRightInit ==
    /\ pc = "ms_copy_right_init"
    /\ j' = m + 1
    /\ pc' = "ms_copy_right"
    /\ UNCHANGED <<a, b, N, stack, l, r, i, k, m>>

MsCopyRight ==
    /\ pc = "ms_copy_right"
    /\ IF j <= r
       THEN /\ b' = [b EXCEPT ![r + m + 1 - j] = a[j]]
            /\ j' = j + 1
            /\ pc' = "ms_copy_right"
            /\ UNCHANGED <<a, N, stack, l, r, i, k, m>>
       ELSE /\ pc' = "ms_merge_init"
            /\ UNCHANGED <<a, b, N, stack, l, r, i, j, k, m>>

MsMergeInit ==
    /\ pc = "ms_merge_init"
    /\ i' = l
    /\ j' = r
    /\ k' = l
    /\ pc' = "ms_merge"
    /\ UNCHANGED <<a, b, N, stack, l, r, m>>

MsMerge ==
    /\ pc = "ms_merge"
    /\ IF k <= r
       THEN /\ IF b[i] <= b[j]
               THEN /\ a' = [a EXCEPT ![k] = b[i]]
                    /\ i' = i + 1
                    /\ UNCHANGED j
               ELSE /\ a' = [a EXCEPT ![k] = b[j]]
                    /\ j' = j - 1
                    /\ UNCHANGED i
            /\ k' = k + 1
            /\ pc' = "ms_merge"
            /\ UNCHANGED <<b, N, stack, l, r, m>>
       ELSE /\ pc' = "ms_return"
            /\ UNCHANGED <<a, b, N, stack, l, r, i, j, k, m>>

MsReturn ==
    /\ pc = "ms_return"
    /\ IF stack = <<>>
       THEN /\ pc' = "Done"
            /\ UNCHANGED <<a, b, N, stack, l, r, i, j, k, m>>
       ELSE /\ Return
            /\ UNCHANGED <<a, b, N>>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Main
    \/ MsStart
    \/ MsLeft
    \/ MsRight
    \/ MsCopyLeftInit
    \/ MsCopyLeft
    \/ MsCopyRightInit
    \/ MsCopyRight
    \/ MsMergeInit
    \/ MsMerge
    \/ MsReturn
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

IsSorted == \A x, y \in DOMAIN a : x < y => a[x] <= a[y]

Invariant == (pc = "Done") => IsSorted

PossibleCounts ==
    /\ TLCGet("stats").states.distinct = 12
    /\ TLCGet("stats").behavior.actions["MsMerge"] = 8

==========================================================================