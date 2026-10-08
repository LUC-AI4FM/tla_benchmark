```
MODULE Quicksort
EXTENDS Integers, Sequences

CONSTANTS ArrayLen
VARIABLES pc, stack, array

Init ==
  /\ pc = "Start"
  /\ stack = << >>
  /\ array = [i \in 1..ArrayLen |-> i]

Next ==
  /\ (pc = "Start") =>
    /\ pc' = "QS"
    /\ stack' = <<1, ArrayLen>>
    /\ array' = array
  /\ (pc = "QS") =>
    /\ (stack # << >>) 
    /\ LET 
        idx == Head(Head(stack))
      IN
      /\ pc' = "Partition"
      /\ stack' = Tail(stack)
      /\ array' = [array EXCEPT ![idx] = Choose({x \in 1..ArrayLen : x <= ArrayLen})]
  /\ (pc = "Partition") =>
    /\ LET 
        idx == Head(Head(stack))
        pivot == array[idx]
        left == [i \in 1..ArrayLen |-> IF i < idx THEN i ELSE i + 1]
      IN
      /\ pc' = "QS"
      /\ stack' = <<left, ArrayLen - 1>> @@ stack
      /\ array' = [array EXCEPT ! = Permute(array, left)]
  /\ (pc = "Done") => 
    /\ UNCHANGED pc
    /\ UNCHANGED stack
    /\ UNCHANGED array

Spec == Init /\ [][Next]_<<pc, stack, array>>
          /\ WF_<<pc, stack, array>>(Next)

THEOREM Spec => <>[]pc = "Done"
```