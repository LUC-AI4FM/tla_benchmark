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
  /\ IF pc = "Start" THEN
    /\ pc' = "Sort"
    /\ array' = array
    /\ b' = <<>>
    /\ stack' = <<"Sort", 1, ArrayLen>>>
  ELSEIF pc = "Sort" THEN
    /\ IF Head(stack) = "Sort" THEN
      /\ LET len == stack[2] - stack[1] + 1
      /\ IF len <= 1 THEN
        /\ pc' = "Done"
        /\ array' = array
        /\ b' = b
        /\ stack' = Tail(stack)
      ELSE
        /\ LET mid == (stack[1] + stack[2]) \div 2
        /\ pc' = "Sort"
        /\ array' = array
        /\ b' = b
        /\ stack' = <<"Sort", stack[1], mid>, "Merge", stack[1], mid, stack[2]>> ^ Tail(Tail(stack))
      END
    ELSEIF Head(stack) = "Merge" THEN
      /\ LET left == stack[1]
      /\ LET mid == stack[2]
      /\ LET right == stack[3]
      /\ IF left <= mid THEN
        /\ pc' = "Merge"
        /\ array' = [array EXCEPT ![left] = b[1]]
        /\ b' = Tail(b)
        /\ stack' = <<left + 1, mid, right>> ^ Tail(Tail(Tail(stack)))
      ELSEIF mid < right THEN
        /\ pc' = "Merge"
        /\ array' = [array EXCEPT ![mid + 1] = b[1]]
        /\ b' = Tail(b)
        /\ stack' = <<left, mid + 1, right>> ^ Tail(Tail(Tail(stack)))
      ELSE
        /\ pc' = "Done"
        /\ array' = array
        /\ b' = b
        /\ stack' = Tail(Tail(Tail(stack)))
      END
    END
  ELSE
    /\ UNCHANGED <<pc, array, b, stack>>
  END

Spec ==
  /\ Init
  /\ [][Next]_<<pc, array, b, stack>>
  /\ WF_<<pc, array, b, stack>>(Next)

Sorted ==
  \A i \in 1..ArrayLen - 1 : array[i] <= array[i + 1]

THEOREM Spec => []<>(pc = "Done" => Sorted)
```