------------------------------- MODULE QuickSort -------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS ArrayLen

VARIABLES Ainit, A, pc, stack, qlo, qhi, pivot

Init == /\ Ainit \in [1..ArrayLen -> 1..ArrayLen]
        /\ A = Ainit
        /\ pc = "main"
        /\ stack = << >>
        /\ qlo = UNDEF
        /\ qhi = UNDEF
        /\ pivot = UNDEF

QS ==
    /\ IF pc = "qs1" THEN
           \/ /\ qhi - qlo <= 1
              /\ pc' = "qs4"
           \/ /\ qhi - qlo > 1
              /\ pivot \in {qlo..qhi}
              /\ A' = [A EXCEPT ![k] = CHOOSE v \in {A[k] : k \in qlo..qhi} :
                              \A i \in qlo..pivot : A[i] <= v
                              /\ \A j \in pivot+1..qhi : v <= A[j]]
              /\ pc' = "qs2"
    [] [\E x \in stack : pc = x[3]] /\
       \/ /\ pc = "qs2" 
          /\ qlo' = qlo
          /\ qhi' = pivot
          /\ stack' = <<qlo, qhi, "qs3">> \o stack
          /\ pc' = "QS"
       \/ /\ pc = "qs3"
          /\ qlo' = pivot + 1
          /\ qhi' = qhi
          /\ stack' = <<qlo, qhi, "qs4">> \o stack
          /\ pc' = "QS"
       \/ /\ pc = "qs4"
          /\ <<qlo', qhi', pc'>> \in [stack]
          /\ stack' = Tail(stack)

Next == 
    /\ IF pc = "main" THEN
           /\ qlo' = 1
           /\ qhi' = ArrayLen
           /\ pc' = "QS"
           /\ UNCHANGED <<A, Ainit, stack>>
       [] QS

Spec == Init /\ [][Next]_<<A, Ainit, pc, stack, qlo, qhi, pivot>> /\ WF_next(<<A, Ainit, pc, stack, qlo, qhi, pivot>>)

Termination ==
    <>(pc = "Done")

THEOREM Spec => []<>(pc = "test") /\ Termination

=============================================================================