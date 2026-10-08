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
  IF pc = "Start" THEN
    /\ pc' = "Sort"
    /\ array' = array
    /\ b' = <<>>
    /\ stack' = <<["array", 1, ArrayLen]>>
  ELSE IF pc = "Sort" THEN
    /\ IF Len(stack) = 0 THEN 
        /\ pc' = "Done"
        /\ UNCHANGED array
        /\ UNCHANGED b
        /\ UNCHANGED stack
      ELSE 
        /\ LET <<l, r>> == Head(Tail(stack)) IN
          /\ IF l < r THEN
              /\ LET m == (l + r) \div 2 IN
                /\ pc' = "Sort"
                /\ array' = array
                /\ b' = Append(b, <<>>)
                /\ stack' = Append(Tail(stack), <<["array", l, m]>>)
                /\ stack' = Append(stack', <<["array", m + 1, r]>>)
            ELSE 
              /\ pc' = "Merge"
              /\ array' = array
              /\ b' = b
              /\ stack' = Tail(stack)
    ELSE IF pc = "Merge" THEN
      /\ LET <<l, r>> == Head(Tail(stack)) IN
        /\ IF l < r THEN
            /\ LET m == (l + r) \div 2 IN
              /\ pc' = "Merge"
              /\ array' = array
              /\ b' = Append(b, <<Min(array[l], array[m])>>)
              /\ stack' = Tail(stack)
          ELSE 
            /\ pc' = "Sort"
            /\ array' = array
            /\ b' = b
            /\ stack' = Tail(stack)

Spec == Init /\ [][Next]_<<pc, array, b, stack>>
  
Termination == <>(pc = "Done")
Fairness == WF_(Next)_(pc)

Sorted(array) == 
  \A i, j \in DOMAIN array : i <= j => array[i] <= array[j]

Safety == []<>(pc = "Done" => Sorted(array))

THEOREM Spec => []Termination
THEOREM Spec => Safety
```