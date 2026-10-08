------------------------------ MODULE PlusCalSpec ------------------------------
EXTENDS Sequences, SETS

VARIABLES x, y, pc

Init ==
  /\ x = {"a", "b"}
  /\ y = <<1, 2, 3>>
  /\ pc = "Init"

PrintT == 
  Print(x) /\ Print(y)

StepInit ==
  /\ pc = "Init"
  /\ x' = x \cup {"c"}
  /\ y' = <<y[1], 4, y[3]>>
  /\ PrintT
  /\ pc' = "Done"

Terminate ==
  /\ pc = "Done"
  /\ UNCHANGED <<x, y, pc>>

Next == StepInit \/ Terminate

Spec == Init /\ [][Next]_vars

Termination == <> (pc = "Done")
===============================================================================