```
MODULE SmallPlusCal
EXTENDS Integers

CONSTANTS 

VARIABLES x, pc

Init == (x \in 1..10) /\ (pc = "Start")

Next == 
  IF pc = "Start" THEN 
    ASSERT x ^ 2 <= 100;
    pc' = "Done"
    ELSE 
      pc' = pc
  ENDIF
  /\ x' = x

Spec == Init /\ [][Next]_<<x, pc>>
           /\ WF_<<x, pc>>(pc = "Start" -> pc' = "Done")

Termination == <>[]pc = "Done"
```