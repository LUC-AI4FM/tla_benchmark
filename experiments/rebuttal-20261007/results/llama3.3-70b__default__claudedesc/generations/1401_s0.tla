```
MODULE Github725b
EXTENDS Integers

CONSTANTS 

VARIABLES outerX

Inner725b == INSTANCE InnerModule WITH x <- outerX

InnerModule == MODULE
  VARIABLE x

  Step == x < 3 /\ x' = x + 1

  Fairness == WF_x(Step)
END InnerModule

Init == outerX = 0

Next == Svc!Step \/ (outerX' = outerX)

Spec == Init /\ [][Next]_outerX /\ Svc!Fairness

Prop == <> (outerX = 3)

THEOREM Spec => Prop
```