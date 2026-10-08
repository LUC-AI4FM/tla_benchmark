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
    /\ IF (stack # << >>)
      THEN
        /\ LET <<l, r>> == Head(stack) IN
          /\ IF l <= r
            THEN
              /\ pc' = "Partition"
              /\ stack' = Tail(stack)
              /\ array' = [array EXCEPT !p = CHOOSE p \in l..r : TRUE]
            ELSE
              /\ pc' = "QS"
              /\ stack' = << >>
              /\ array' = array
          ELSE
    /\ (pc = "Partition") =>
      /\ LET <<l, r>> == Head(stack) IN
        /\ IF l <= r
          THEN
            /\ pc' = "Swap"
            /\ stack' = <<l, r>> @@ <<l + 1, r>>
            /\ array' = [array EXCEPT !l = array[r]]
          ELSE
            /\ pc' = "QS"
            /\ stack' = << >>
            /\ array' = array
  /\ (pc = "Swap") =>
    /\ LET <<l, r>> == Head(stack) IN
      /\ IF l < r
        THEN
          /\ pc' = "Swap"
          /\ stack' = <<l + 1, r - 1>>
          /\ array' = [array EXCEPT !l = array[r]]
        ELSE
          /\ pc' = "QS"
          /\ stack' = << >>
          /\ array' = array
  /\ (pc = "Done") =>
    /\ UNCHANGED pc
    /\ UNCHANGED stack
    /\ UNCHANGED array

Spec ==
  /\ Init
  /\ [][Next]_<<pc, stack, array>>
  /\ WF_<<pc, stack, array>>(Next)

THEOREM Spec => <>[]pc = "Done"
```
Note that this TLA+ specification is a direct translation of the given natural language description and might require some adjustments to fit specific requirements or constraints not mentioned in the problem statement.