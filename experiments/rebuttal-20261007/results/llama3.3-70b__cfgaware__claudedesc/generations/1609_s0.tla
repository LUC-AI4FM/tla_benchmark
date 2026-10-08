---------------------------- MODULE Quicksort ----------------------------
EXTENDS Integers

CONSTANT ArrayLen

VARIABLE Ainit, A, pc, stack, qlo, qhi, pivot

Init == (* Initialize the state *)
        /\ Ainit \in [1..ArrayLen -> 1..ArrayLen]
        /\ A = Ainit
        /\ pc = "main"
        /\ stack = << >>
        /\ qlo = 0
        /\ qhi = 0
        /\ pivot = 0

qs1 == (* Select a pivot and partition the array *)
        /\ pc = "qs1"
        /\ qlo < qhi
        /\ pivot \in qlo..qhi
        /\ A' = [A EXCEPT !i \in qlo..pivot : A'[i] <= A[pivot]]
        /\ A' = [A EXCEPT !i \in (pivot+1)..qhi : A'[i] >= A[pivot]]
        /\ pc' = "qs2"
        /\ UNCHANGED <<stack, qlo, qhi>>

qs2 == (* Recursively call QS on the left sub-array *)
        /\ pc = "qs2"
        /\ stack' = Append(stack, <<qlo, qhi>>)
        /\ qlo' = qlo
        /\ qhi' = pivot - 1
        /\ pc' = "main"
        /\ UNCHANGED <<A, pivot>>

qs3 == (* Recursively call QS on the right sub-array *)
        /\ pc = "qs3"
        /\ stack' = Append(stack, <<qlo, qhi>>)
        /\ qlo' = pivot + 1
        /\ qhi' = qhi
        /\ pc' = "main"
        /\ UNCHANGED <<A, pivot>>

qs4 == (* Return from the recursive call *)
        /\ pc = "qs4"
        /\ stack # << >>
        /\ <<qlo', qhi'>> = Head(stack)
        /\ stack' = Tail(stack)
        /\ pc' = IF qlo' = 1 AND qhi' = ArrayLen THEN "Done" ELSE "test"
        /\ UNCHANGED <<A, pivot>>

main == (* Start the quicksort algorithm *)
        /\ pc = "main"
        /\ qlo' = 1
        /\ qhi' = ArrayLen
        /\ pc' = "qs1"
        /\ UNCHANGED <<stack, A, pivot>>

test == (* Assert that A is sorted and a permutation of Ainit *)
        /\ pc = "test"
        /\ A # << >>
        /\ Perm(A, Ainit)
        /\ Sorted(A)
        /\ pc' = "Done"
        /\ UNCHANGED <<A, stack, qlo, qhi, pivot>>

Next == (* The next-state relation *)
        \/ main
        \/ qs1
        \/ qs2
        \/ qs3
        \/ qs4
        \/ test

Spec == (* The temporal specification *)
        Init /\ [][Next]_<<A, pc, stack, qlo, qhi, pivot>> /\ WF_vars(Next)

Termination == (* The checked property *)
        <>pc = "Done"

=============================================================================