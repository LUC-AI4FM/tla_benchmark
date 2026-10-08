```tla
MODULE EvenOdd

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS N

VARIABLES pc, stack, xEven, xOdd, result

Init == 
  /\ pc = "Start"
  /\ stack = << >>
  /\ xEven = 0
  /\ xOdd = 0
  /\ result = FALSE

Next ==
  \/ /\ pc = "Start"
     /\ UNCHANGED <<stack, xEven, xOdd, result>>
     /\ pc' = IF N % 2 = 0 THEN "Even" ELSE "Odd"
  \/ /\ pc = "Even"
     /\ stack = << >>
     /\ xEven = 0
     /\ result = FALSE
     /\ pc' = "Done"
     /\ result' = TRUE
  \/ /\ pc = "Odd"
     /\ stack = << >>
     /\ xOdd = 0
     /\ result = FALSE
     /\ pc' = "Done"
     /\ result' = FALSE

Spec ==
  WF_vars(<<pc, stack, xEven, xOdd, result>>, Next) /\
  Init \/ [][Next]_<<pc, stack, xEven, xOdd, result>> \/
  <>(pc = "Done")

```