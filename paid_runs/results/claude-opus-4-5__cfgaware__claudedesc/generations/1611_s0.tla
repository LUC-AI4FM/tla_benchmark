---------------------------- MODULE specification ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT ArrayLen
CONSTANT defaultInitValue

VARIABLES a, b, pc, stack, l, r, i, j, k, m

vars == <<a, b, pc, stack, l, r, i, j, k, m>>

Init ==
    /\ \E N \in 0..ArrayLen:
        /\ a \in [1..N -> 1..N]
        /\ b = [x \in 1..N |-> defaultInitValue]
    /\ pc = "start"
    /\ stack = <<>>
    /\ l = defaultInitValue
    /\ r = defaultInitValue
    /\ i = defaultInitValue
    /\ j = defaultInitValue
    /\ k = defaultInitValue
    /\ m = defaultInitValue

Len1(f) == 
    LET S == DOMAIN f
    IN IF S = {} THEN 0
       ELSE LET max == CHOOSE x \in S : \A y \in S : y <= x
            IN max

Start ==
    /\ pc = "start"
    /\ IF Len1(a) > 0
       THEN /\ l' = 1
            /\ r' = Len1(a)
            /\ stack' = <<>>
            /\ pc' = "ms1"
       ELSE /\ pc' = "Done"
            /\ l' = l
            /\ r' = r
            /\ stack' = stack
    /\ UNCHANGED <<a, b, i, j, k, m>>

MS1 ==
    /\ pc = "ms1"
    /\ IF l < r
       THEN /\ m' = (l + r) \div 2
            /\ stack' = Append(stack, [procedure |-> "mergesort", l |-> l, r |-> r, i |-> i, j |-> j, k |-> k, m |-> m, returnTo |-> "ms2"])
            /\ r' = m'
            /\ i' = defaultInitValue
            /\ j' = defaultInitValue
            /\ k' = defaultInitValue
            /\ pc' = "ms1"
            /\ UNCHANGED l
       ELSE /\ pc' = "ms_return"
            /\ UNCHANGED <<stack, l, r, i, j, k, m>>
    /\ UNCHANGED <<a, b>>

MS2 ==
    /\ pc = "ms2"
    /\ stack' = Append(stack, [procedure |-> "mergesort", l |-> l, r |-> r, i |-> i, j |-> j, k |-> k, m |-> m, returnTo |-> "ms3"])
    /\ l' = m + 1
    /\ i' = defaultInitValue
    /\ j' = defaultInitValue
    /\ k' = defaultInitValue
    /\ pc' = "ms1"
    /\ UNCHANGED <<a, b, r, m>>

MS3 ==
    /\ pc = "ms3"
    /\ i' = l
    /\ pc' = "copy1"
    /\ UNCHANGED <<a, b, stack, l, r, j, k, m>>

Copy1 ==
    /\ pc = "copy1"
    /\ IF i <= m
       THEN /\ b' = [b EXCEPT ![i] = a[i]]
            /\ i' = i + 1
            /\ pc' = "copy1"
       ELSE /\ j' = m + 1
            /\ pc' = "copy2"
            /\ UNCHANGED <<b, i>>
    /\ UNCHANGED <<a, stack, l, r, k, m>>

Copy2 ==
    /\ pc = "copy2"
    /\ IF j <= r
       THEN /\ b' = [b EXCEPT ![r + m + 1 - j] = a[j]]
            /\ j' = j + 1
            /\ pc' = "copy2"
       ELSE /\ i' = l
            /\ j' = r
            /\ k' = l
            /\ pc' = "merge"
            /\ UNCHANGED b
    /\ UNCHANGED <<a, stack, l, r, m>>

Merge ==
    /\ pc = "merge"
    /\ IF k <= r
       THEN /\ IF b[i] <= b[j]
               THEN /\ a' = [a EXCEPT ![k] = b[i]]
                    /\ i' = i + 1
                    /\ UNCHANGED j
               ELSE /\ a' = [a EXCEPT ![k] = b[j]]
                    /\ j' = j - 1
                    /\ UNCHANGED i
            /\ k' = k + 1
            /\ pc' = "merge"
       ELSE /\ pc' = "ms_return"
            /\ UNCHANGED <<a, i, j, k>>
    /\ UNCHANGED <<b, stack, l, r, m>>

MSReturn ==
    /\ pc = "ms_return"
    /\ IF stack = <<>>
       THEN /\ pc' = "Done"
            /\ UNCHANGED <<stack, l, r, i, j, k, m>>
       ELSE /\ LET frame == Head(stack)
               IN /\ l' = frame.l
                  /\ r' = frame.r
                  /\ i' = frame.i
                  /\ j' = frame.j
                  /\ k' = frame.k
                  /\ m' = frame.m
                  /\ pc' = frame.returnTo
                  /\ stack' = Tail(stack)
    /\ UNCHANGED <<a, b>>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Start
    \/ MS1
    \/ MS2
    \/ MS3
    \/ Copy1
    \/ Copy2
    \/ Merge
    \/ MSReturn
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

IsSorted(arr) ==
    LET dom == DOMAIN arr
    IN \A x, y \in dom : x < y => arr[x] <= arr[y]

Invariant ==
    pc = "Done" => IsSorted(a)

PossibleCounts ==
    /\ TLCGet("stats").distinct = 12
    /\ TRUE

=============================================================================