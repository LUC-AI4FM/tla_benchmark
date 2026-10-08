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
  /\ x = x

Spec ==
  Init /\ [][Next]_<<x, y>>
```
Note: This TLA+ module assumes that the `Integers` module is available, which provides basic integer operations and constants. If this is not the case, you may need to modify the module accordingly or include additional definitions for integer-related operators and constants.