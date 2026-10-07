----------------------------- MODULE SmallStateMachine -----------------------------
EXTENDS Integers

VARIABLES x, y

Foo(a, f) == IF a = 1 THEN [f EXCEPT ![a] = 42] ELSE f

Init ==
  /\ x \in 1..5
  /\ y = [i \in 1..5 |-> 0]

Next ==
  /\ x' = x
  /\ y' = Foo(x, y)

Spec == Init /\ [][Next]_<<x, y>>
=============================================================================