```
MODULE Mergesort
EXTENDS Integers, Sequences

CONSTANTS ArrayLen, N
VARIABLES pc, array, b, stack

Init ==
  /\ pc = "Start"
  /\ array \in [1..ArrayLen -> 1..N]
  /\ b = <<>>
  /\ stack = <<>>

Next ==
  /\ (pc = "Start") =>
    /\ pc' = "Sort"
    /\ array' = array
    /\ b' = <<>>
    /\ stack' = <<["array", 1, ArrayLen]>>
  /\ (pc = "Sort") =>
    /\ IF Head(stack) = ["array", 1, ArrayLen]
      THEN
        /\ pc' = "Split"
        /\ array' = array
        /\ b' = b
        /\ stack' = Tail(stack) @@ <<["array", 1, ArrayLen \div 2], ["array", ArrayLen \div 2 + 1, ArrayLen]>>
      ELSE
        /\ pc' = "Merge"
        /\ array' = array
        /\ b' = b
        /\ stack' = Tail(stack)
    /\ (pc = "Split") =>
      /\ IF Head(stack) = ["array", 1, ArrayLen \div 2]
        THEN
          /\ pc' = "Sort"
          /\ array' = array
          /\ b' = b
          /\ stack' = <<["array", 1, ArrayLen \div 2]>>
        ELSE
          /\ pc' = "Done"
          /\ array' = array
          /\ b' = b
          /\ stack' = <<>>
    /\ (pc = "Merge") =>
      /\ IF Head(stack) = ["array", ArrayLen \div 2 + 1, ArrayLen]
        THEN
          /\ pc' = "Sort"
          /\ array' = array
          /\ b' = b
          /\ stack' = <<["array", ArrayLen \div 2 + 1, ArrayLen]>>
        ELSE
          /\ pc' = "Done"
          /\ array' = Merge(array, b)
          /\ b' = <<>>
          /\ stack' = <<>>
    /\ (pc = "Done") =>
      /\ UNCHANGED pc
      /\ UNCHANGED array
      /\ UNCHANGED b
      /\ UNCHANGED stack

Spec ==
  /\ Init
  /\ [][Next]_<<pc, array, b, stack>>
  /\ WF_<<pc, array, b, stack>>(Next)

Sorted(a) ==
  \A i, j \in Domain a : i <= j => a[i] <= a[j]

Merge(a, b) ==
  IF b = <<>> THEN a
  ELSE LET left == a[1..Len(a) \div 2]
           right == a[Len(a) \div 2 + 1..Len(a)]
       IN Merge(left, b) @@ Merge(right, b)

THEOREM Spec => []<>(pc = "Done" /\ Sorted(array))
```