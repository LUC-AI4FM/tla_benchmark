```
MODULE SmallPlusCal
EXTENDS Naturals, Sequences

VARIABLES x, y, pc

Init ==
  /\ x = {"a", "b"}
  /\ y = <<1, 2, 3>>
  /\ pc = "Init"

UpdateStep ==
  /\ pc = "Init"
  /\ x' = x ∪ {"c"}
  /\ y' = [i \in 1..Len(y) |-> IF i = 2 THEN 4 ELSE y[i]]
  /\ pc' = "Done"

TerminatingStutter ==
  /\ pc = "Done"
  /\ x' = x
  /\ y' = y
  /\ pc' = pc

Next == UpdateStep \/ TerminatingStutter

Spec == Init /\ [][Next]_vars

Termination == <> (pc = "Done")
```