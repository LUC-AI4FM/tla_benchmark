---------------------------- MODULE RecursiveMergesort ----------------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS ArrayLen

VARIABLES pc, i, j, k, m, n, a, b, stack

Init == /\ pc = "Start"
        /\ i \in 1..ArrayLen
        /\ a \in [1..ArrayLen -> Int]
        /\ b \in [1..ArrayLen -> Int]
        /\ stack = <<>>

Next ==
    \/ /\ pc = "Start"
       /\ UNCHANGED <<i, j, k, m, n, a, b>>
       /\ stack = <<>>
       /\ pc' = "Sort"

    \/ /\ pc = "Sort"
       /\ i \in 1..ArrayLen
       /\ j \in 1..ArrayLen
       /\ i <= j
       /\ m = (i + j) DIV 2
       /\ pc' = "PushLeft"
       /\ stack' = Append(stack, <<i, m>>)

    \/ /\ pc = "Sort"
       /\ i \in 1..ArrayLen
       /\ j \in 1..ArrayLen
       /\ i > j
       /\ pc' = "Done"

    \/ /\ pc = "PushLeft"
       /\ UNCHANGED <<i, j, k, m, n, a, b>>
       /\ pc' = "Sort"

    \/ /\ pc = "Pop"
       /\ stack \= <<>>
       /\ LET top == Head(stack)
            i_ == first(top)
            m_ == second(top)
        IN /\ i' = i_
           /\ j' = m_
           /\ k = m_ + 1
           /\ n = j
           /\ pc' = "PushRight"
           /\ stack' = Tail(stack)

    \/ /\ pc = "Pop"
       /\ stack = <<>>
       /\ pc' = "Merge"

    \/ /\ pc = "PushRight"
       /\ UNCHANGED <<i, j, k, m, n, a, b>>
       /\ pc' = "Sort"

    \/ /\ pc = "Merge"
       /\ LET i_ == i
            j_ == j
        IN /\ /\ n - i_ + 1 \geq 2
           /\ \A x \in i_..m : b[x] = a[x]
           /\ \A x \in m+1..n : b[x] = a[x]
           /\ k' = i_
           /\ pc' = "MergeLoop"
       [] \/ n - i_ + 1 < 2
          /\ UNCHANGED <<i, j, k, m, n, b>>
          /\ pc' = "Pop"

    \/ /\ pc = "MergeLoop"
       /\ LET i_ == i
            j_ == j
        IN /\ /\ k \leq n
           /\ (k > m \/ a[k] >= b[i_])
           /\ (k <= m \/ b[j_] < a[k])
           /\ pc' = "CopyA"
       [] \/ k > n
          /\ UNCHANGED <<i, j, k, m>>
          /\ pc' = "Pop"

    \/ /\ pc = "CopyA"
       /\ LET i_ == i
            j_ == j
        IN /\ a[k] = b[i_]
           /\ i_' = i_ + 1
           /\ k' = k + 1
           /\ pc' = "MergeLoop"

    \/ /\ pc = "Done"
       /\ UNCHANGED <<i, j, k, m, n, a, b, stack>>

Spec == Init /\ [][Next]_<<pc, i, j, k, m, n, a, b, stack>> /\ <>[]WF_pc(Next)

Sorted(seq) == \A x \in 1..Len(seq)-1 : seq[x] <= seq[x+1]

Termination == <>[](pc = "Done")

Safety == \/ pc \= "Done"
          \/ Sorted(a[1..ArrayLen])

Liveness == Termination

THEOREM Spec => []Safety /\ Liveness

=============================================================================