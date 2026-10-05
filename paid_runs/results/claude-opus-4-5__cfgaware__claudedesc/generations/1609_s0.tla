---------------------------- MODULE quicksort ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT ArrayLen

VARIABLES Ainit, A, pc, stack, qlo, qhi, pivot

vars == <<Ainit, A, pc, stack, qlo, qhi, pivot>>

ArrayType == [1..ArrayLen -> 1..ArrayLen]

Len(arr) == ArrayLen

IsPermutation(arr1, arr2) ==
    /\ DOMAIN arr1 = DOMAIN arr2
    /\ \A v \in 1..ArrayLen : 
        Cardinality({i \in DOMAIN arr1 : arr1[i] = v}) = 
        Cardinality({i \in DOMAIN arr2 : arr2[i] = v})

IsSorted(arr) ==
    \A i, j \in 1..ArrayLen : i < j => arr[i] <= arr[j]

PartitionInvariant(arr, lo, hi, p) ==
    /\ p >= lo /\ p <= hi
    /\ \A i \in lo..p : \A j \in (p+1)..hi : arr[i] <= arr[j]

PreservesOutside(arr1, arr2, lo, hi) ==
    \A i \in 1..ArrayLen : (i < lo \/ i > hi) => arr2[i] = arr1[i]

Init ==
    /\ Ainit \in ArrayType
    /\ A = Ainit
    /\ pc = "main"
    /\ stack = <<>>
    /\ qlo = 1
    /\ qhi = 1
    /\ pivot = 1

main ==
    /\ pc = "main"
    /\ stack' = <<[procedure |-> "QS", pc |-> "test", qlo |-> qlo, qhi |-> qhi, pivot |-> pivot]>> \o stack
    /\ qlo' = 1
    /\ qhi' = ArrayLen
    /\ pivot' = 1
    /\ pc' = "qs1"
    /\ UNCHANGED <<Ainit, A>>

qs1 ==
    /\ pc = "qs1"
    /\ IF qhi > qlo
       THEN \E p \in qlo..qhi :
            \E Anew \in ArrayType :
                /\ PreservesOutside(A, Anew, qlo, qhi)
                /\ IsPermutation(A, Anew)
                /\ PartitionInvariant(Anew, qlo, qhi, p)
                /\ A' = Anew
                /\ pivot' = p
                /\ pc' = "qs2"
       ELSE /\ pc' = "qs4"
            /\ UNCHANGED <<A, pivot>>
    /\ UNCHANGED <<Ainit, stack, qlo, qhi>>

qs2 ==
    /\ pc = "qs2"
    /\ stack' = <<[procedure |-> "QS", pc |-> "qs3", qlo |-> qlo, qhi |-> qhi, pivot |-> pivot]>> \o stack
    /\ qhi' = pivot
    /\ pivot' = 1
    /\ pc' = "qs1"
    /\ UNCHANGED <<Ainit, A, qlo>>

qs3 ==
    /\ pc = "qs3"
    /\ stack' = <<[procedure |-> "QS", pc |-> "qs4", qlo |-> qlo, qhi |-> qhi, pivot |-> pivot]>> \o stack
    /\ qlo' = pivot + 1
    /\ pivot' = 1
    /\ pc' = "qs1"
    /\ UNCHANGED <<Ainit, A, qhi>>

qs4 ==
    /\ pc = "qs4"
    /\ IF stack # <<>>
       THEN /\ pc' = Head(stack).pc
            /\ qlo' = Head(stack).qlo
            /\ qhi' = Head(stack).qhi
            /\ pivot' = Head(stack).pivot
            /\ stack' = Tail(stack)
       ELSE /\ pc' = "test"
            /\ UNCHANGED <<stack, qlo, qhi, pivot>>
    /\ UNCHANGED <<Ainit, A>>

test ==
    /\ pc = "test"
    /\ Assert(IsPermutation(A, Ainit), "A must be permutation of Ainit")
    /\ Assert(IsSorted(A), "A must be sorted")
    /\ pc' = "Done"
    /\ UNCHANGED <<Ainit, A, stack, qlo, qhi, pivot>>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ main
    \/ qs1
    \/ qs2
    \/ qs3
    \/ qs4
    \/ test
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

==========================================================================