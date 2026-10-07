```
MODULE EvenOdd
EXTENDS Integers, Sequences

CONSTANTS N

VARIABLES pc, result, stack, xEven, xOdd

Init ==
  /\ pc = "Start"
  /\ result = FALSE
  /\ stack = <<>>
  /\ xEven = 0
  /\ xOdd = 0

Next ==
  IF pc = "Start" THEN
    /\ pc' = "Even"
    /\ result' = result
    /\ stack' = Append(stack, "Even")
    /\ xEven' = N
    /\ xOdd' = 0
  ELSE IF pc = "Even" THEN
    IF xEven = 0 THEN
      /\ pc' = "Done"
      /\ result' = TRUE
      /\ stack' = Tail(stack)
      /\ xEven' = xEven
      /\ xOdd' = xOdd
    ELSE
      /\ pc' = "Odd"
      /\ result' = result
      /\ stack' = Append(stack, "Odd")
      /\ xEven' = xEven
      /\ xOdd' = xEven - 1
  ELSE IF pc = "Odd" THEN
    IF xOdd = 0 THEN
      /\ pc' = "Done"
      /\ result' = FALSE
      /\ stack' = Tail(stack)
      /\ xEven' = xEven
      /\ xOdd' = xOdd
    ELSE
      /\ pc' = "Even"
      /\ result' = result
      /\ stack' = Append(stack, "Even")
      /\ xEven' = xOdd - 1
      /\ xOdd' = xOdd
  ELSE
    /\ pc' = pc
    /\ result' = result
    /\ stack' = stack
    /\ xEven' = xEven
    /\ xOdd' = xOdd

Spec ==
  /\ Init
  /\ [][Next]_<<pc, result, stack, xEven, xOdd>>
  /\ WF_<<pc, result, stack, xEven, xOdd>>(Next)

Termination ==
  <> (pc = "Done")

InOdd == pc = "Odd"
CallOdd == pc = "Odd" /\ ~ (SeqPrefix(stack, 1) = "Odd")

PossibleCounts ==
  /\ [][InOdd => InOdd']_InOdd
  /\ [][CallOdd => CallOdd']_CallOdd
  /\ <<InOdd, CallOdd>> \in TLC._POSSIBLE

THEOREM Spec => []Termination
THEOREM Spec => PossibleCounts
```