------------------------------ MODULE SmallStateMachine ------------------------------

EXTENDS Integers

CONSTANTS DOMAIN
ASSUME DOMAIN = 1..5

VARIABLES x, y

Foo(y, x) ==
  IF x = 1 THEN [y EXCEPT ![x] = 42] ELSE y

Init ==
  /\ x \in DOMAIN
  /\ y = [i \in DOMAIN |-> 0]

Next ==
  /\ UNCHANGED x
  /\ y' = Foo(y, x)

Spec ==
  Init /\ [] [Next]_<<x, y>>

=============================================================================