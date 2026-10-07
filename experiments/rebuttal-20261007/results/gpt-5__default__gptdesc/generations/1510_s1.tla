------------------------------- MODULE SmallStateMachine -------------------------------

EXTENDS Integers

VARIABLES x, y

Foo(y, x) ==
  IF x = 1 THEN [y EXCEPT ![x] = 42] ELSE y

Init ==
  /\ x \in 1..5
  /\ y = [i \in 1..5 |-> 0]

Next ==
  /\ x' = x
  /\ y' = Foo(y, x)

Spec ==
  Init /\ [][Next]_<<x, y>>

=============================================================================