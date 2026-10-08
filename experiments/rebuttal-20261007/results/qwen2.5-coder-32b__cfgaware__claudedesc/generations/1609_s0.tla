------------------------------- MODULE QuickSort -------------------------------

CONSTANTS ArrayLen

VARIABLES Ainit, A, pc, stack, qlo, qhi, pivot

(*--algorithm QuickSort
variables Ainit = [1..ArrayLen -> CHOOSE x \in 1..ArrayLen: TRUE],
          A = Ainit,
          pc = "main",
          stack = <<>>,
          qlo = 0,
          qhi = 0,
          pivot = 0;

fair process (P) = begin
main:
    pc := "qs1";
    qlo := 1;
    qhi := ArrayLen;
qs1:
    if qlo >= qhi then
        /\ IF stack /= <<>> THEN
            /\ pc := "qs4"
           ELSE
            /\ pc := "test"
         FI
    else
        pivot := CHOOSE p \in qlo..qhi: TRUE;
        A := [i \in 1..ArrayLen |->
                IF i < qlo \/ i > qhi THEN A[i]
                ELSE IF A[i] <= A[pivot] THEN A[CHOOSE j \in qlo..pivot: A[j] = A[i]]
                     ELSE A[CHOOSE j \in pivot+1..qhi: A[j] = A[i]]];

        stack := <<stack, qlo, pivot+1, qhi>>;
        pc := "qs2";
qs2:
    qlo := qlo;
    qhi := pivot;
    pc := "qs1";
qs3:
    qlo := CHOOSE l \in 1..ArrayLen: <<l, h>> \in Tail(stack);
    qhi := CHOOSE h \in 1..ArrayLen: <<l, h>> \in Tail(stack);
    stack := Head(stack);
    pc := "qs1";
qs4:
    IF stack /= <<>> THEN
        /\ qlo := CHOOSE l \in 1..ArrayLen: <<l, h>> \in Tail(stack);
        /\ qhi := CHOOSE h \in 1..ArrayLen: <<l, h>> \in Tail(stack);
        /\ stack := Head(stack);
    FI;
    pc := "qs4";
test:
    ASSERT A = [i \in 1..ArrayLen -> CHOOSE x \in 1..ArrayLen: TRUE] \* Placeholder for permutation check
         /\ \A i \in 1..ArrayLen-1: A[i] <= A[i+1];
    pc := "Done";
end process;
end algorithm;*)

Next == \/ pc = "main" -> /\ qlo' = 1
                             /\ qhi' = ArrayLen
                             /\ pc' = "qs1"
          \/ pc = "qs1" -> (\/ qlo >= qhi -> (\/ stack /= <<>> -> /\ pc' = "qs4"
                                                                 ELSE /\ pc' = "test")
                              \/ /\ pivot' \in qlo..qhi
                                 /\ A' = [i \in 1..ArrayLen |->
                                             IF i < qlo \/ i > qhi THEN A[i]
                                             ELSE IF A[i] <= A[pivot'] THEN A[CHOOSE j \in qlo..pivot': A[j] = A[i]]
                                                  ELSE A[CHOOSE j \in pivot'+1..qhi: A[j] = A[i]]]
                                 /\ stack' = <<stack, qlo, pivot'+1, qhi>>
                                 /\ pc' = "qs2")
          \/ pc = "qs2" -> /\ qlo' = qlo
                             /\ qhi' = pivot'
                             /\ pc' = "qs1"
          \/ pc = "qs3" -> /\ qlo' = CHOOSE l \in 1..ArrayLen: <<l, h>> \in Tail(stack)
                             /\ qhi' = CHOOSE h \in 1..ArrayLen: <<l, h>> \in Tail(stack)
                             /\ stack' = Head(stack)
                             /\ pc' = "qs1"
          \/ pc = "qs4" -> (\/ stack /= <<>> -> /\ qlo' = CHOOSE l \in 1..ArrayLen: <<l, h>> \in Tail(stack)
                                                   /\ qhi' = CHOOSE h \in 1..ArrayLen: <<l, h>> \in Tail(stack)
                                                   /\ stack' = Head(stack)
                                                   /\ pc' = "qs4"
                              \/ pc' = "test")
          \/ pc = "test" -> /\ A' = [i \in 1..ArrayLen -> CHOOSE x \in 1..ArrayLen: TRUE] \* Placeholder for permutation check
                               /\ \A i \in 1..ArrayLen-1: A[i] <= A[i+1]
                               /\ pc' = "Done"

Init == /\ Ainit \in [1..ArrayLen -> 1..ArrayLen]
        /\ A = Ainit
        /\ pc = "main"
        /\ stack = <<>>
        /\ qlo = 0
        /\ qhi = 0
        /\ pivot = 0

Spec == Init /\ [][Next]_<<A, pc, stack, qlo, qhi, pivot>>

Termination == <>(pc = "Done")

=============================================================================