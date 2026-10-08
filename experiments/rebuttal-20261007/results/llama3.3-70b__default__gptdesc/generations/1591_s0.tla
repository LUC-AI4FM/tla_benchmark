```
MODULE EvenOdd
EXTENDS Integers

CONSTANTS N

VARIABLES pc, stack, xEven, xOdd, result

Init ==
  /\ pc = "Start"
  /\ stack = << >>
  /\ xEven = 0
  /\ xOdd = 0
  /\ result = FALSE

Next ==
  \/ (pc = "Start" /\ pc' = "Even" /\ stack' = <<N>> @@ stack /\ xEven' = N /\ xOdd' = 0 /\ result' = result)
  \/ (pc = "Even" /\ xEven > 0 /\ pc' = "Odd" /\ stack' = <<xEven - 1>> @@ stack /\ xEven' = xEven - 1 /\ xOdd' = xEven /\ result' = result)
  \/ (pc = "Even" /\ xEven = 0 /\ pc' = "Done" /\ stack' = Tail(stack) /\ xEven' = xEven /\ xOdd' = xOdd /\ result' = TRUE)
  \/ (pc = "Odd" /\ xOdd > 0 /\ pc' = "Even" /\ stack' = <<xOdd - 1>> @@ stack /\ xEven' = xOdd /\ xOdd' = xOdd - 1 /\ result' = result)
  \/ (pc = "Odd" /\ xOdd = 0 /\ pc' = "Done" /\ stack' = Tail(stack) /\ xEven' = xEven /\ xOdd' = xOdd /\ result' = FALSE)
  \/ (pc = "Done" /\ pc' = pc /\ stack' = stack /\ xEven' = xEven /\ xOdd' = xOdd /\ result' = result)

Spec ==
  /\ Init
  /\ [][Next]_<<pc, stack, xEven, xOdd, result>>
  /\ WF_<<pc, stack, xEven, xOdd, result>>(Next)
  /\ []<>(pc = "Done")

THEOREM Spec => []<>(pc = "Done")
```