---------------------------- MODULE MergeSort ----------------------------
EXTENDS Integers, Sequences

CONSTANT ArrayLen

VARIABLE a, b, stack, pc

defaultInitValue == [i \in 1..ArrayLen |-> i]

Invariant == 
  (pc = "Done") => a = SortSeq(a)

Spec == 
  /\ Init
  /\ [][Next]_(a, b, stack, pc)
  /\ WF_(a, b, stack, pc)(Next)

Termination == <>("Done" \in pc)

Init ==
  /\ a \in [1..ArrayLen -> 1..ArrayLen]
  /\ b = defaultInitValue
  /\ stack = <<>>
  /\ pc = "Start"

SortSeq(s) == 
  LET sorted == << >>
  IN 
    sorted = s \/ (sorted = [s |-> s[1]] @ [i \in 2..Len(s) |-> s[i]])

Next ==
  /\ (pc = "Start") => 
      pc' = "mergesort" 
      /\ stack' = <<1, ArrayLen>>
      /\ UNCHANGED <<a, b>>
  /\ (pc = "mergesort") => 
      /\ stack # <<>> 
      /\ LET l == Head(stack), r == stack[2] IN
          /\ l <= r 
          /\ IF l < r THEN
              /\ pc' = "midpoint"
              /\ stack' = <<l, (l + r) \div 2>, (l + r) \div 2 + 1, r>> @ Tail(Tail(stack))
              /\ UNCHANGED <<a, b>>
            ELSE 
              /\ pc' = "Done"
              /\ stack' = Tail(stack)
              /\ UNCHANGED <<a, b>>
      /\ UNCHANGED <<a, b>>
  /\ (pc = "midpoint") => 
      /\ LET l == Head(stack), r == stack[2], m == (l + r) \div 2 IN
          /\ pc' = "copy_left"
          /\ stack' = <<l, m, m + 1, r>> @ Tail(Tail(stack))
          /\ b' = [i \in l..m |-> a[i]] @ [i \in (m+1)..r |-> a[r - i + m + 1]]
          /\ UNCHANGED a
      /\ UNCHANGED pc
  /\ (pc = "copy_left") => 
      /\ LET l == Head(stack), r == stack[3] IN
          /\ IF l <= r THEN
              /\ pc' = "copy_right"
              /\ b' = [i \in l..r |-> a[i]] @ [j \in (r+1)..ArrayLen |-> b[j]]
              /\ UNCHANGED <<stack, a>>
            ELSE 
              /\ pc' = "merge"
              /\ stack' = Tail(Tail(stack))
              /\ UNCHANGED <<a, b>>
      /\ UNCHANGED pc
  /\ (pc = "copy_right") => 
      /\ LET l == Head(stack), r == stack[3] IN
          /\ IF l <= r THEN
              /\ pc' = "merge"
              /\ a' = [i \in l..r |-> b[i]] @ [j \in (r+1)..ArrayLen |-> a[j]]
              /\ UNCHANGED <<stack, b>>
            ELSE 
              /\ pc' = "Done"
              /\ stack' = Tail(stack)
              /\ UNCHANGED <<a, b>>
      /\ UNCHANGED pc
  /\ (pc = "merge") => 
      /\ LET l == Head(stack), r == stack[2] IN
          /\ IF l <= r THEN
              /\ pc' = "Done"
              /\ a' = [i \in l..r |-> b[i]] @ [j \in (r+1)..ArrayLen |-> a[j]]
              /\ UNCHANGED <<stack, b>>
            ELSE 
              /\ pc' = "mergesort"
              /\ stack' = <<l, r>> @ Tail(Tail(stack))
              /\ UNCHANGED <<a, b>>
      /\ UNCHANGED pc
  /\ (pc = "Done") => 
      /\ UNCHANGED <<stack, a, b, pc>>

=============================================================================