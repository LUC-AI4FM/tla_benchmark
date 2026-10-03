---------------------------- MODULE Quicksort ----------------------------
EXTENDS Integers, Sequences

CONSTANT ArrayLen

VARIABLE pc, stack, array

Init ==
  /\ pc = "Start"
  /\ stack = << >>
  /\ array = [i \in 1..ArrayLen |-> i]

Next ==
  \/ (pc = "Start") /\ QS(1, ArrayLen)
  \/ (pc = "QS") /\ QS_Step
  \/ (pc = "Done")

Spec == Init /\ [][Next]_<<pc, stack, array>>
           /\ WF_<<pc, stack, array>>(Next)

Termination == <>[]pc = "Done"

QS(p, q) ==
  /\ pc' = "QS"
  /\ stack' = <<p, q>> @@ stack
  /\ array' = array

QS_Step ==
  /\ pc = "QS"
  /\ <<p, q>> = Head(stack)
  /\ pivot \in p..q
  /\ Perm(p, q, array, array')
  /\ Partition(p, q, pivot, array', array)
  /\ stack' = Tail(stack)
  /\ IF p < q THEN pc' = "QS" ELSE pc' = "Done"

Perm(p, q, a, b) ==
  \A i \in 1..ArrayLen \ {p..q} : a[i] = b[i]

Partition(p, q, pivot, a, b) ==
  /\ \A i \in p..pivot : a[i] <= a[pivot]
  /\ \A i \in (pivot+1)..q : a[pivot] < a[i]
  /\ \A i \in p..q : \E j \in p..q : a[j] = b[i]

THEOREM Spec => []Termination
=============================================================================