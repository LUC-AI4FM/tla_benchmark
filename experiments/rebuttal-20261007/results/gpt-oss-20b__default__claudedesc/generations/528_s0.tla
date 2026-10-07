MODULE PlusCalExample
EXTENDS Naturals, Sequences, SETS

VARIABLES x, y, pc

Init ==
  /\ x = {"a", "b"}
  /\ y = <<1,2,3>>
  /\ pc = "Start"

Lbl_1 ==
  /\ pc = "Start"
  /\ x' = x \cup {"c"}
  /\ y' = [i \in 1..#y |-> IF i=2 THEN 4 ELSE y[i]]
  /\ pc' = "Done"
  /\ PrintT(x')
  /\ PrintT(y')

Terminating ==
  /\ pc = "Done"
  /\ x' = x
  /\ y' = y
  /\ pc' = "Done"

Next == Lbl_1 \/ Terminating

vars == <<x, y, pc>>

Spec == Init /\ [][Next]_vars

Termination == <> (pc = "Done")