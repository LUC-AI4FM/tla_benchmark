------------------------------ MODULE SmallSM ------------------------------
EXTENDS Integers

VARIABLES x, y

Init ==
  /\ x \in 1..5
  /\ y = [i \in 1..5 |-> 0]

Foo(xVal, f) ==
  IF xVal = 1 THEN
    [f EXCEPT ![xVal] = 42]
  ELSE
    f

Next ==
  /\ UNCHANGED <<x>>
  /\ y' = Foo(x, y)

Spec == Init /\ [] [Next]_<<x,y>>

=============================================================================