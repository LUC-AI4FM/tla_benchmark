```
MODULE PlusCalAlgorithm
EXTENDS Integers, TLC, Sequences

CONSTANTS 

VARIABLES x, y, pc

Init ==
  /\ x = {"a", "b"}
  /\ y = <<1, 2, 3>>
  /\ pc = "Start"

Next ==
  /\ pc = "Start"
  /\ x' = x \cup {"c"}
  /\ y' = [y EXCEPT ![2] = 4]
  /\ PrintT(x')
  /\ PrintT(y')
  /\ pc' = "Done"

Terminating ==
  /\ pc = "Done"
  /\ UNCHANGED <<x, y, pc>>

Spec == Init /\ [][Next]_vars
          /\ WF_vars(Terminating)

THEOREM Spec => <>pc = "Done"
```