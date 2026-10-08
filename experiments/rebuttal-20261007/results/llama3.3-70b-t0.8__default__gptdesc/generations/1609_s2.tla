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
  /\ pc = "Start" =>
    /\ pc' = "QS"
    /\ stack' = <<1, ArrayLen>>
    /\ array' = array
  \/ pc = "QS" =>
    /\ (pc' = "Partition" /\ stack' = Append(stack, << > >>) /\ array' = array)
      \/ (pc' = "Done" /\ stack' = Tail(stack) /\ array' = array)
  \/ pc = "Partition" =>
    /\ (pc' = "QS" /\ stack' = Append(stack, << > >>) /\ array' \in [a \in Seq(ArrayLen) | 
        a[1..(Head(Head(stack)) - 1)] = array[1..(Head(Head(stack)) - 1)]
        /\ a[(Head(Head(stack)) + 1)..(Tail(Tail(stack))) ] = array[(Head(Head(stack)) + 1)..(Tail(Tail(stack)))]
        /\ a[(Head(Head(stack)))] <= a[(Head(Head(stack)) + 1)..(Tail(Tail(stack)))]
        ])
      \/ (pc' = "Done" /\ stack' = Tail(stack) /\ array' = array)
  \/ pc = "Done" => 
    /\ UNCHANGED <<pc, stack, array>>

Spec == Init /\ [][Next]_<<pc, stack, array>>
           /\ WF_<<pc, stack, array>>(Next)

THEOREM Spec => <>[]pc = "Done"
```