```
MODULE EvenOdd
EXTENDS Integers, Sequences

CONSTANTS N

VARIABLES pc, stack, xEven, xOdd, result

Init ==
  /\ pc = "Start"
  /\ stack = << >>
  /\ xEven = 0
  /\ xOdd = 0
  /\ result = FALSE

Next == 
  \/ (pc = "Start" ∧ 
      pc' = "Even" 
      ∧ stack' = Append(stack, <<N>>) 
      ∧ xEven' = N 
      ∧ xOdd' = 0 
      ∧ result' = result)
  \/ (pc = "Even" ∧ 
      xEven > 0 
      ∧ pc' = "Odd" 
      ∧ stack' = Append(stack, <<xEven - 1>>) 
      ∧ xEven' = xEven 
      ∧ xOdd' = xEven - 1 
      ∧ result' = result)
  \/ (pc = "Even" ∧ 
      xEven = 0 
      ∧ pc' = "Done" 
      ∧ stack' = Tail(stack) 
      ∧ xEven' = xEven 
      ∧ xOdd' = xOdd 
      ∧ result' = TRUE)
  \/ (pc = "Odd" ∧ 
      xOdd > 0 
      ∧ pc' = "Even" 
      ∧ stack' = Append(stack, <<xOdd - 1>>) 
      ∧ xEven' = xOdd - 1 
      ∧ xOdd' = xOdd 
      ∧ result' = result)
  \/ (pc = "Odd" ∧ 
      xOdd = 0 
      ∧ pc' = "Done" 
      ∧ stack' = Tail(stack) 
      ∧ xEven' = xEven 
      ∧ xOdd' = xOdd 
      ∧ result' = FALSE)
  \/ (pc = "Done" 
      ∧ UNCHANGED <<pc, stack, xEven, xOdd, result>>)

Spec == Init ∧ [][Next]_<<pc, stack, xEven, xOdd, result>>
           ∧ WF_<<pc, stack, xEven, xOdd, result>>(Next)
           ∧ []<>(pc = "Done")

THEOREM Spec => []<>(pc = "Done")
```