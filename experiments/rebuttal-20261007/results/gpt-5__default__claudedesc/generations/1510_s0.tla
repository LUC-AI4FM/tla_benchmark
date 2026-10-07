------------------------------ MODULE J ------------------------------

EXTENDS Naturals

VARIABLES x, y

S == 1..5

Foo(fx, fy) == IF fx = 1 THEN [fy EXCEPT ![fx] = 42] ELSE fy

Init ==
  /\ x \in S
  /\ y = [i \in S |-> 0]

Next ==
  /\ x' = x
  /\ y' = Foo(x, y)

Spec == Init /\ [][Next]_<<x, y>>

=============================================================================