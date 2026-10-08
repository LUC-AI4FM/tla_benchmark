MODULE SmallSM
EXTENDS Naturals

VARIABLES x, y

Init ==
  /\ 1 <= x /\ x <= 5
  /\ y = [i \in 1..5 |-> 0]

Foo(f, i) ==
  IF i = 1 THEN [f EXCEPT ![i] = 42]
  ELSE f

Next ==
  /\ x' = x
  /\ y' = Foo(y, x)

Spec == Init /\ [] [Next]_<<x,y>>