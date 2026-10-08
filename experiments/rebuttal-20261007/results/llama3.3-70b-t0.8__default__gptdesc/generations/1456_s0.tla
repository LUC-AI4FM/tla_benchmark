```tla
MODULE TinyStateMachine
EXTENDS Integers, TLC

CONSTANTS 
  InitX, InitY

VARIABLES 
  x, y

Init == 
  (x = InitX) /\
  (y = InitY)

FullSet(x) == 
  (x = {1, 2, 3})

GainThree(x, x') == 
  (3 \in x') /\ (3 \notin x)

Next == 
  y' = y /\ 
  x' \subseteq y' /\ 
  FullSet(x') => GainThree(x, x')

Spec == 
  Init /\ [][Next]_<<x, y>>

THEOREM TLCGet("FullSet", "ModelChecking") = 5
THEOREM TLCGet("GainThree", "ModelChecking") = 3

=============================================================================
```