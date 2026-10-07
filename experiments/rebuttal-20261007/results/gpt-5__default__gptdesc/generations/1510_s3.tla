----------------------------- MODULE SmallStateMachine -----------------------------
EXTENDS Integers

CONSTANTS Dom
ASSUME Dom = 1..5

VARIABLES x, y

vars == << x, y >>

Foo(f, xv) == IF xv = 1 THEN [f EXCEPT ![xv] = 42] ELSE f

Init ==
  /\ x \in Dom
  /\ y = [i \in Dom |-> 0]

Next ==
  /\ UNCHANGED x
  /\ y' = Foo(y, x)

Spec ==
  Init /\ [][Next]_vars
============================================================================