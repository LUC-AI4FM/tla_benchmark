```
MODULE SmallStateMachine
EXTENDS Integers

CONSTANTS 

VARIABLES x, y

Init ==
  /\ x \in 1..5
  /\ y = [i \in {1,2,3,4,5} |-> 0]

Foo(f, x) == 
  IF x = 1 THEN [f EXCEPT ![1] = 42] ELSE f

Next ==
  y' = Foo(y, x)
  /\ x' = x

Spec == Init /\ [][Next]_<<x, y>>
```