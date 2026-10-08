```
MODULE PlusCalAlgorithm
EXTENDS Integers, TLC, Sequences
CONSTANTS 
VARIABLES x, y, pc

Init ==
  (x = {"a", "b"}) /\ (y = <<1, 2, 3>>) /\ (pc = "Start")

Next ==
  IF pc = "Start"
  THEN
    (x' = x \cup {"c"}) /\ 
    (y' = [y EXCEPT ![2] = 4]) /\ 
    (PrintT("x =", x)) /\ 
    (PrintT("y =", y)) /\ 
    (pc' = "Done")
  ELSE
    (x' = x) /\ (y' = y) /\ (pc' = pc)

Terminating ==
  (pc = "Done")

Spec == Init /\ [][Next]_vars

THEOREM Spec => []<>Terminating
```