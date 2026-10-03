---------------------------- MODULE quicksort ----------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT ArrayLen

ASSUME ArrayLen \in Nat /\ ArrayLen >= 0

VARIABLES arr, arr0, pc, stack, lo, hi

vars == <<arr, arr0, pc, stack, lo, hi>>

Perms(S) == {f \in [S -> S] : \A y \in S : \E x \in S : f[x] = y}

IsPermutation(a, b) ==
    /\ DOMAIN a = DOMAIN b
    /\ \E perm \in Perms(DOMAIN a) : \A i \in DOMAIN a : a[i] = b[perm[i]]

IsSorted(a) ==
    \A i, j \in DOMAIN a : i <= j => a[i] <= a[j]

Init ==
    /\ arr \in [1..ArrayLen -> 1..ArrayLen]
    /\ arr0 = arr
    /\ pc = "Start"
    /\ stack = <<>>
    /\ lo = 1
    /\ hi = ArrayLen

Partition(a, l, h) ==
    {a2 \in [1..ArrayLen -> 1..ArrayLen] :
        /\ \A i \in 1..ArrayLen : (i < l \/ i > h) => a2[i] = a[i]
        /\ \E perm \in Perms(l..h) : \A i \in l..h : a2[i] = a[perm[i]]
        /\ \E p \in l..h :
            /\ \A i \in l..p : \A j \in (p+1)..h : a2[i] <= a2[j]
    }

Start ==
    /\ pc = "Start"
    /\ IF lo < hi
       THEN pc' = "Recurse"
       ELSE IF stack = <<>>
            THEN pc' = "Done"
            ELSE /\ pc' = "Return"
    /\ UNCHANGED <<arr, arr0, stack, lo, hi>>

Recurse ==
    /\ pc = "Recurse"
    /\ lo < hi
    /\ \E a2 \in Partition(arr, lo, hi) :
        \E pivot \in lo..hi :
            /\ (\A i \in lo..pivot : \A j \in (pivot+1)..hi : a2[i] <= a2[j])
            /\ arr' = a2
            /\ stack' = Append(stack, [lo |-> lo, hi |-> hi, pivot |-> pivot, phase |-> 1])
            /\ hi' = pivot
            /\ UNCHANGED lo
    /\ pc' = "Start"
    /\ UNCHANGED arr0

Return ==
    /\ pc = "Return"
    /\ stack # <<>>
    /\ LET frame == Head(stack)
       IN IF frame.phase = 1
          THEN /\ stack' = Append(Tail(stack), [lo |-> frame.lo, hi |-> frame.hi, pivot |-> frame.pivot, phase |-> 2])
               /\ lo' = frame.pivot + 1
               /\ hi' = frame.hi
               /\ pc' = "Start"
          ELSE /\ stack' = Tail(stack)
               /\ lo' = frame.lo
               /\ hi' = frame.hi
               /\ pc' = IF Tail(stack) = <<>> THEN "CheckDone" ELSE "Return"
    /\ UNCHANGED <<arr, arr0>>

CheckDone ==
    /\ pc = "CheckDone"
    /\ pc' = "Done"
    /\ UNCHANGED <<arr, arr0, stack, lo, hi>>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Start
    \/ Recurse
    \/ Return
    \/ CheckDone
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

Sorted == IsSorted(arr)

PermutationPreserved == IsPermutation(arr, arr0)

FinalCorrect == pc = "Done" => (Sorted /\ PermutationPreserved)

==========================================================================