```
MODULE SmallPlusCal
EXTENDS Integers

CONSTANTS 

VARIABLES x, pc

Init == (x \in 1..10) /\ (pc = "Start")

Next == 
  IF pc = "Start" THEN 
    assert x^2 <= 100;
    pc' = "Done"
    ELSE 
      pc' = pc
  ENDIF
  /\ x' = x

Spec == Init /\ [][Next]_<<x,pc>>
Termination == <>[] (pc = "Done")

THEOREM Spec => Termination
```