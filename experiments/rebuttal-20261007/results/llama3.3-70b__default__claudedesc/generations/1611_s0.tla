```tla
MODULE MergeSort
EXTENDS Integers, Sequences

CONSTANTS ArrayLen

VARIABLES a, b, stack, pc, i, j, k, m

Init ==
  /\ a \in [1..ArrayLen -> 1..ArrayLen]
  /\ b = << >>
  /\ stack = <<"mergesort", 1, ArrayLen >>
  /\ pc = "Start"
  /\ i = 0
  /\ j = 0
  /\ k = 0
  /\ m = 0

Next ==
  \/ pc = "Start" /\ stack # << >> /\ 
    (pc' = "mergesort" /\ stack' = Tail(stack) 
     /\ a' = a /\ b' = b /\ i' = i /\ j' = j /\ k' = k /\ m' = m)
  \/ pc = "mergesort" /\ stack # << >> /\ Head(Head(stack)) = "mergesort" /\
    (m' = (Len(stack) - 2) \div 2
     /\ i' = Head(Tail(stack))
     /\ j' = Head(Tail(Tail(stack)))
     /\ pc' = "midpoint"
     /\ stack' = stack
     /\ a' = a
     /\ b' = b
     /\ k' = k)
  \/ pc = "mergesort" /\ stack # << >> /\ Head(Head(stack)) = "mergesort" /\
    (m' = (j - i + 1) \div 2
     /\ pc' = "left"
     /\ stack' = <<<<"mergesort", i, m + i - 1 >>>> @ Tail(stack)
     /\ a' = a
     /\ b' = b
     /\ k' = k)
  \/ pc = "mergesort" /\ stack # << >> /\ Head(Head(stack)) = "mergesort" /\
    (m' = m
     /\ pc' = "right"
     /\ stack' = <<<<"mergesort", m + i, j >>>> @ Tail(stack)
     /\ a' = a
     /\ b' = b
     /\ k' = k)
  \/ pc = "left" /\ stack # << >> /\ Head(Head(stack)) = "mergesort" /\
    (pc' = "copy_left"
     /\ stack' = stack
     /\ a' = a
     /\ b' = b
     /\ i' = i
     /\ j' = j
     /\ k' = 1)
  \/ pc = "left" /\ stack # << >> /\ Head(Head(stack)) = "mergesort" /\
    (k' < m - i + 1
     /\ b' = [b EXCEPT ![k] = a[i + k - 1]]
     /\ pc' = "copy_left"
     /\ stack' = stack
     /\ a' = a
     /\ i' = i
     /\ j' = j
     /\ k' = k + 1)
  \/ pc = "left" /\ stack # << >> /\ Head(Head(stack)) = "mergesort" /\
    (k = m - i + 1
     /\ pc' = "right"
     /\ stack' = Tail(stack)
     /\ a' = a
     /\ b' = b
     /\ i' = m + i
     /\ j' = j
     /\ k' = 1)
  \/ pc = "right" /\ stack # << >> /\ Head(Head(stack)) = "mergesort" /\
    (pc' = "copy_right"
     /\ stack' = stack
     /\ a' = a
     /\ b' = b
     /\ i' = i
     /\ j' = j
     /\ k' = 1)
  \/ pc = "right" /\ stack # << >> /\ Head(Head(stack)) = "mergesort" /\
    (k' < j - m + 1
     /\ b' = [b EXCEPT ![m + i + k] = a[j - k + 1]]
     /\ pc' = "copy_right"
     /\ stack' = stack
     /\ a' = a
     /\ i' = i
     /\ j' = j
     /\ k' = k + 1)
  \/ pc = "right" /\ stack # << >> /\ Head(Head(stack)) = "mergesort" /\
    (k = j - m + 1
     /\ pc' = "merge"
     /\ stack' = Tail(stack)
     /\ a' = a
     /\ b' = b
     /\ i' = i
     /\ j' = j
     /\ k' = 1)
  \/ pc = "merge" /\ stack # << >> /\ Head(Head(stack)) = "mergesort" /\
    (pc' = "merge_loop"
     /\ stack' = stack
     /\ a' = a
     /\ b' = b
     /\ i' = i
     /\ j' = j
     /\ k' = 1)
  \/ pc = "merge" /\ stack # << >> /\ Head(Head(stack)) = "mergesort" /\
    (k < j - i + 2
     /\ a' = [a EXCEPT ![i + k - 1] = IF b[k] <= b[j - k + 1] THEN b[k] ELSE b[j - k + 1]]
     /\ pc' = "merge_loop"
     /\ stack' = stack
     /\ b' = b
     /\ i' = i
     /\ j' = j
     /\ k' = k + 1)
  \/ pc = "merge" /\ stack # << >> /\ Head(Head(stack)) = "mergesort" /\
    (k = j - i + 2
     /\ pc' = "Done"
     /\ stack' = << >>
     /\ a' = a
     /\ b' = b
     /\ i' = i
     /\ j' = j
     /\ k' = k)
  \/ pc = "Done" /\ UNCHANGED <<a, b, stack, pc, i, j, k, m >>

Invariant ==
  (pc = "Done") => a[1..Len(a)] = Sort(a[1..Len(a)])

Termination == <>("Done" = pc)

Spec == Init /\ [][Next]_<<a, b, stack, pc, i, j, k, m>> /\ WF_<<a, b, stack, pc, i, j, k, m>>(Next)

THEOREM Spec => []Invariant
THEOREM Spec => Termination

POSTCONDITION PossibleCounts == 
  (TLC.numStates = 12) /\ (TLC.numMergeSteps = 8)
```