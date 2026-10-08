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
  IF pc = "Start" THEN
    /\ pc' = "Even"
    /\ stack' = Append(<< >>, stack)
    /\ xEven' = N
    /\ xOdd' = 0
    /\ result' = result
  ELSE IF pc = "Even" THEN
    /\ (xEven > 1) => 
        (\* recursive call to Odd \*
        /\ pc' = "Odd"
        /\ stack' = Append(<< xEven - 2 >>, stack)
        /\ xEven' = xEven - 2
        /\ xOdd' = xOdd
        /\ result' = result)
    /\ (xEven = 1) => 
        (\* base case for Even: return FALSE \*
        /\ pc' = "Return"
        /\ stack' = Tail(stack)
        /\ xEven' = Head(stack)
        /\ xOdd' = xOdd
        /\ result' = FALSE)
    /\ (xEven = 0) => 
        (\* base case for Even: return TRUE \*
        /\ pc' = "Return"
        /\ stack' = Tail(stack)
        /\ xEven' = Head(stack)
        /\ xOdd' = xOdd
        /\ result' = TRUE)
  ELSE IF pc = "Odd" THEN
    /\ (xOdd > 1) => 
        (\* recursive call to Even \*
        /\ pc' = "Even"
        /\ stack' = Append(<< xOdd - 2 >>, stack)
        /\ xEven' = xEven
        /\ xOdd' = xOdd - 2
        /\ result' = result)
    /\ (xOdd = 1) => 
        (\* base case for Odd: return TRUE \*
        /\ pc' = "Return"
        /\ stack' = Tail(stack)
        /\ xEven' = xEven
        /\ xOdd' = Head(stack)
        /\ result' = TRUE)
    /\ (xOdd = 0) => 
        (\* base case for Odd: return FALSE \*
        /\ pc' = "Return"
        /\ stack' = Tail(stack)
        /\ xEven' = xEven
        /\ xOdd' = Head(stack)
        /\ result' = FALSE)
  ELSE IF pc = "Return" THEN
    /\ pc' = "Done"
    /\ stack' = << >>
    /\ xEven' = xEven
    /\ xOdd' = xOdd
    /\ result' = result
  ELSE 
    (\* allow infinite stuttering \*
    /\ pc' = pc
    /\ stack' = stack
    /\ xEven' = xEven
    /\ xOdd' = xOdd
    /\ result' = result)

Spec == Init /\ [][Next]_<<pc, stack, xEven, xOdd, result>>
Termination == <>[]<>(pc = "Done")
Fairness == WF_Next(Next)
THEOREM Spec => []Termination
```