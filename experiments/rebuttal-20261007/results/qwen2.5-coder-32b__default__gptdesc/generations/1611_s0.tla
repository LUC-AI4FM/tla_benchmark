------------------------------- MODULE RecursiveMergesort -------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS ArrayLen

VARIABLES pc, i, j, k, n, a, b, stack

Init == 
  /\ pc = "Start"
  /\ i \in 1..ArrayLen
  /\ a \in [1..ArrayLen -> Nat]
  /\ b \in [1..2*ArrayLen -> Nat]
  /\ stack = <<>>

Next ==
  \/ /\ pc = "Start"
     /\ n' = i
     /\ pc' = "Sort"
  \/ /\ pc = "Sort"
     /\ n > 1
     /\ stack' = Append(stack, <<n, "Merge">>)
     /\ n' = n \div 2
     /\ pc' = "Sort"
  \/ /\ pc = "Sort"
     /\ n <= 1
     /\ pc' = "Return"
  \/ /\ pc = "Merge"
     /\ LET m == FIRST(stack)[1]
        r == m - (m \div 2)
        l == m \div 2
        i == 1
        j == 1
        k == 1
     IN /\ b' = [b EXCEPT ![k] = a[1]]
        /\ pc' = "MergeLoop"
  \/ /\ pc = "MergeLoop"
     /\ i <= l
     /\ j <= r
     /\ (a[i] <= a[l+j] => /\ b'[k] = a[i]
                             /\ i' = i + 1)
     /\ (a[i] > a[l+j] => /\ b'[k] = a[l+j]
                            /\ j' = j + 1)
     /\ k' = k + 1
     /\ pc' = "MergeLoop"
  \/ /\ pc = "MergeLoop"
     /\ i > l
     /\ j <= r
     /\ b'[k] = a[l+j]
     /\ j' = j + 1
     /\ k' = k + 1
     /\ pc' = "MergeLoop"
  \/ /\ pc = "MergeLoop"
     /\ i <= l
     /\ j > r
     /\ b'[k] = a[i]
     /\ i' = i + 1
     /\ k' = k + 1
     /\ pc' = "MergeLoop"
  \/ /\ pc = "MergeLoop"
     /\ i > l
     /\ j > r
     /\ LET m == FIRST(stack)[1]
        r == m - (m \div 2)
        l == m \div 2
     IN /\ a' = [a EXCEPT ![k] = b[k] : k \in 1..m]
        /\ stack' = Tail(stack)
        /\ pc' = "Return"
  \/ /\ pc = "Return"
     /\ stack # <<>>
     /\ LET m == FIRST(stack)[1]
        r == m - (m \div 2)
        l == m \div 2
     IN /\ n' = m
        /\ pc' = "Merge"
  \/ /\ pc = "Return"
     /\ stack = <<>>
     /\ pc' = "Done"

Spec ==
  /\ Init
  /\ [][Next]_<<pc, i, j, k, n, a, b, stack>>
  /\ WF_[Next]_<<pc, i, j, k, n, a, b, stack>>

Sorted(seq) == \A x \in seq, y \in seq : (x <= y)

Safety ==
  \/ pc # "Done"
  \/ Sorted(a[1..n])

Liveness ==
  <>[](pc = "Done")

THEOREM Spec => []Safety /\ Liveness
=============================================================================