```
MODULE SimpleAlgorithm
EXTENDS Integers, Sequences, TLC

CONSTANTS 

VARIABLES x, y, pc

Init ==
  (x = {"a", "b"}) /\ (y = <<1, 2, 3>>) /\ (pc = "Lbl_1")

Next ==
  IF pc = "Lbl_1" THEN
    /\ x' = x \cup {"c"}
    /\ y' = [y EXCEPT ![2] = 4]
    /\ PrintT("x:", x')
    /\ PrintT("y:", y')
    /\ pc' = "Done"
  ELSE
    /\ Terminating
    /\ UNCHANGED <<x, y, pc>>

Terminating == (pc' = pc) /\ UNCHANGED <<x, y>>

Spec == Init /\ [][Next]_<<x, y, pc>>
Termination == <>(pc = "Done")

THEOREM Spec => []Termination
```