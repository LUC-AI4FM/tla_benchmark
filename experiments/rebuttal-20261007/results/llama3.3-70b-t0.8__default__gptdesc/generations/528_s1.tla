```
MODULE PlusCalAlgorithm
EXTENDS Integers, TLC, Sequences

CONSTANTS 
  Done

VARIABLES 
  x,
  y,
  pc

Init ==
  (x = {"a", "b"}) /\
  (y = <<1, 2, 3>>) /\
  (pc = "Start")

Next ==
  IF pc = "Start" THEN
    /\ x' = x \cup {"c"}
    /\ y' = [y EXCEPT ![2] = 4]
    /\ PrintT("x =", x')
    /\ PrintT("y =", y')
    /\ pc' = "Done"
  ELSE
    /\ x' = x
    /\ y' = y
    /\ pc' = pc

Terminating ==
  pc' = pc

Spec == 
  Init /\ [][Next]_<<x, y, pc>> /\ WF_vars(Terminating)_

THEOREM Spec => <> (pc = "Done")
```