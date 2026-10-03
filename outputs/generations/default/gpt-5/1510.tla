------------------------------ MODULE SmallStateMachine ------------------------------

EXTENDS Integers

CONSTANTS S

ASSUME S = 1..5

VARIABLES x, y

Foo(xv, yf) ==
  IF xv = 1
    THEN [yf EXCEPT ![xv] = 42]
    ELSE yf

Init ==
  /\ x \in S
  /\ y = [i \in S |-> 0]

Next ==
  /\ x' = x
  /\ y' = Foo(x, y)

Spec ==
  Init /\ [][Next]_<<x, y>>

=============================================================================