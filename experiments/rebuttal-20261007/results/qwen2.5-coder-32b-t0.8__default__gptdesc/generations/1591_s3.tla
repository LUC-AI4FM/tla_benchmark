------------------------------- MODULE EvenOdd -------------------------------

EXTENDS Integers, FiniteSets

CONSTANTS N

VARIABLES pc, stack, xEven, xOdd, result

Init == 
  /\ pc = "Start"
  /\ stack = << >>
  /\ xEven = N
  /\ xOdd = N
  /\ result = FALSE

Next ==
  \/ \* In procedure Even
     (pc = "Even" /\
      \/ /\ xEven > 0
         /\ xEven % 2 = 0
         /\ result' = TRUE
         /\ pc' = "Done"
      \/ /\ xEven > 0
         /\ xEven % 2 # 0
         /\ stack' = Append(stack, <<pc, xEven>>)
         /\ pc' = "Odd"
         /\ xOdd' = xEven - 1)
     \/ \* In procedure Odd
     (pc = "Odd" /\
      \/ /\ xOdd > 0
         /\ xOdd % 2 = 0
         /\ result' = FALSE
         /\ pc' = "Done"
      \/ /\ xOdd > 0
         /\ xOdd % 2 # 0
         /\ stack' = Append(stack, <<pc, xOdd>>)
         /\ pc' = "Even"
         /\ xEven' = xOdd - 1)
     \/ \* Start procedure Even
     (pc = "Start" /\
      stack' = << >>
      /\ pc' = "Even")
     \/ \* Return from Odd to Even
     (pc = "Done" /\
      /\ Head(stack) = << "Even", xEven >>
      /\ Tail(stack)' = Tail(stack)
      /\ result' = result)
     \/ \* Return from Even to Odd
     (pc = "Done" /\
      /\ Head(stack) = << "Odd", xOdd >>
      /\ Tail(stack)' = Tail(stack)
      /\ result' = result)

Spec ==
  /\ Init
  /\ [][Next]_<<pc, stack, xEven, xOdd, result>>
  /\ WF_[Next]_<<pc, stack, xEven, xOdd, result>>

THEOREM Spec => []<>pc = "Done"

=============================================================================