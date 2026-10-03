------------------------------ MODULE SmallStateMachine ------------------------------

EXTENDS Integers

VARIABLES x, y

S == 1..5

Init ==
  /\ x \in S
  /\ y = [i \in S |-> 0]

Foo(ax, ay) ==
  IF ax = 1 THEN [ay EXCEPT ![ax] = 42] ELSE ay

Next ==
  /\ x' = x
  /\ y' = Foo(x, y)

Spec == Init /\ [] [Next]_<<x, y>>

====================================================================================