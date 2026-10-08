```
MODULE CounterSystem
EXTENDS Integers
CONSTANTS 
VARIABLES outerX

InnerModule(x) == [* x = 0 *]
                  /\ [][* x' = x + 1 /\ x < 3
                      \/ x' = x /\ ~(x < 3) *]_x
                  /\ WF_v(x)(x < 3)

Init == outerX = 0

Next == (* InnerModule(outerX)
          /\ outerX' = outerX + 1 /\ outerX < 3
         *)
         \/ (* ~(InnerModule(outerX))
              /\ outerX' = outerX
             *)

Spec == Init /\ [][Next]_outerX
          /\ <>[](outerX = 3)

THEOREM Spec => []<>((outerX = 3) /\ (outerX' = outerX))
```