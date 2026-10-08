```
MODULE TinyStateMachine
EXTENDS Integers, TLC
CONSTANTS 
VARIABLES x, y

Init ==
  /\ x \subseteq {1, 2, 3}
  /\ y = {1, 2, 3}

Next ==
  /\ y' = y
  /\ x' \subseteq y

FullSet(x) == x = {1, 2, 3}
GainThree(x, x') == x' = x \cup {3}

Spec == Init /\ [][Next]_

THEOREM TLCGet("FullSet") = 10
THEOREM TLCGet("GainThree") = 5
```