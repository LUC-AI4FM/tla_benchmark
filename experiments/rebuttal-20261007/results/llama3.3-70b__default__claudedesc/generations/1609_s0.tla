```tla
MODULE Quicksort
EXTENDS Integers, Sequences

CONSTANTS ArrayLen

VARIABLES Ainit, A, pc, stack, qlo, qhi, pivot

Init ==
  /\ Ainit \in [1..ArrayLen -> 1..ArrayLen]
  /\ A = Ainit
  /\ pc = "main"
  /\ stack = << >>
  /\ qlo = 0
  /\ qhi = 0
  /\ pivot = 0

Next ==
  \/ (pc = "main") /\ (pc' = "qs1") /\ (stack' = <<1, ArrayLen >>) /\ (qlo' = 1) /\ (qhi' = ArrayLen) /\ (pivot' = 0) /\ UNCHANGED Ainit /\ UNCHANGED A
  \/ (pc = "qs1") /\ qlo < qhi /\ 
    (EXISTS idx \in qlo..qhi : 
      /\ pivot' = idx
      /\ A' = [A EXCEPT !i \in qlo..qhi : IF i <= idx THEN A[i] <= A[idx + 1] ELSE A[i] > A[idx]]
      /\ pc' = "qs2"
      /\ stack' = <<qlo, qhi, idx >> @ stack
      /\ qlo' = qlo
      /\ qhi' = idx
      /\ UNCHANGED Ainit)
  \/ (pc = "qs1") /\ qlo >= qhi /\ 
    (pc' = "qs4") /\ (stack' = Tail(stack)) /\ (qlo' = Head(Head(stack))) /\ (qhi' = Head(Tail(stack))) /\ (pivot' = Head(Tail(Tail(stack)))) /\ UNCHANGED Ainit /\ UNCHANGED A
  \/ (pc = "qs2") /\ 
    (EXISTS idx \in qlo..qhi : 
      /\ pivot' = idx
      /\ pc' = "qs3"
      /\ stack' = <<idx + 1, qhi >> @ stack
      /\ qlo' = idx + 1
      /\ qhi' = qhi
      /\ UNCHANGED Ainit
      /\ UNCHANGED A)
  \/ (pc = "qs3") /\ 
    (EXISTS idx \in qlo..qhi : 
      /\ pivot' = idx
      /\ pc' = "qs4"
      /\ stack' = Tail(stack)
      /\ qlo' = Head(Head(stack))
      /\ qhi' = Head(Tail(stack))
      /\ UNCHANGED Ainit
      /\ UNCHANGED A)
  \/ (pc = "qs4") /\ stack = << >> /\ 
    (pc' = "test") /\ UNCHANGED Ainit /\ UNCHANGED A /\ UNCHANGED stack /\ UNCHANGED qlo /\ UNCHANGED qhi /\ UNCHANGED pivot
  \/ (pc = "test") /\ 
    (A' = A) /\ (pc' = "Done") /\ UNCHANGED Ainit /\ UNCHANGED stack /\ UNCHANGED qlo /\ UNCHANGED qhi /\ UNCHANGED pivot

Spec ==
  Init /\ [][Next]_<<Ainit, A, pc, stack, qlo, qhi, pivot>> /\ WF_<<Ainit, A, pc, stack, qlo, qhi, pivot>>(Next)

Termination == <>(pc = "Done")
```