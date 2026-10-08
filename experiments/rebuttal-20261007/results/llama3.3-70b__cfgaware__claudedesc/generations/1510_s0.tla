---------------------------- MODULE J ----------------------------
EXTENDS Integers

CONSTANT XValues
VARIABLE x, y

x == 1
y == [i \in XValues |-> 0]

Foo(y) ==
  IF x = 1 THEN
    [y EXCEPT ![1] = 42]
  ELSE
    y

Next ==
  y' = Foo(y)

Spec ==
  (x \in {1, 2, 3, 4, 5}) /\ (y = [i \in XValues |-> 0])
  *
  [](Next)

THEOREM Spec => []
====================================================================