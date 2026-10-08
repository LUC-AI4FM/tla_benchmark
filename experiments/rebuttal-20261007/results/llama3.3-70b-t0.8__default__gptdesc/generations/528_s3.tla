```
MODULE PlusCalAlgorithm
EXTENDS Integers, Sequences, TLC

CONSTANTS 
VARIABLES x, y, pc

Init ==
  (x = {"a", "b"}) /\ (y = <<1, 2, 3>>) /\ (pc = "Start")

Next ==
  IF pc = "Start" THEN
    x' = x \cup {"c"} /\ 
    y' = [y EXCEPT ![2] = 4] /\ 
    pc' = "Done" /\ 
    PrintT(x) /\ 
    PrintT(y)
  ELSE
    (x' = x) /\ (y' = y) /\ (pc' = pc)

Terminating ==
  pc = "Done"

Spec == Init /\ [][Next]_<<x, y, pc>> /\ WF_vars(Next) /\ <>Terminating

THEOREM Spec => <>Terminating
```