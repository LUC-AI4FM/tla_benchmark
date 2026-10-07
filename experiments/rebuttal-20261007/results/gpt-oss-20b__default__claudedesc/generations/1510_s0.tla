MODULE J
EXTENDS Integers

VARIABLES x, y

(* Helper operator *)
Foo(x, f) == IF x = 1 THEN [f EXCEPT ![x] = 42] ELSE f

Init ==
  /\ x \in 1..5
  /\ y = [i \in 1..5 |-> 0]

Stutter ==
  /\ x' = x
  /\ y' = y

Next ==
  /\ x' = x
  /\ y' = Foo(x, y)

Spec == Init /\ [] (Next \/ Stutter)