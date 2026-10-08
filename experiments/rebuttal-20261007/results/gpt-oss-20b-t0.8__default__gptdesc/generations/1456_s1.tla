```
MODULE TinySM
EXTENDS SETS

VARIABLE x, y

Init ==
  /\ y ∈ SUBSET {1,2,3}
  /\ x ⊆ y

Next ==
  /\ y' = y
  /\ x' ⊆ y'

FullSet == (x = {1,2,3})

GainThree == (3 ∈ x' /\ 3 ∉ x)

Spec == Init /\ [][Next]_<<x,y>>
```