---- MODULE SmallStateMachine ----

EXTENDS Naturals, FiniteSets, Functions

CONSTANTS Domain
VARIABLES x, y

Foo(y, x) == 
  IF x = 1 THEN [y EXCEPT ![x] = 42]
  ELSE y

Init == /\ x \in {1, 2, 3, 4, 5}
        /\ y = [n \in Domain |-> 0]

Next == /\ UNCHANGED x
          /\ y' = Foo(y, x)

Spec == Init /\ [](Next) <*> <<x, y>>

====