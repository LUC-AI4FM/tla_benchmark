---- MODULE SingleVarTS ----
EXTENDS Naturals

CONSTANTS THREE
ASSUME THREE = 3

VARIABLES x

Init == x = 0

Next ==
  /\ x < THREE
  /\ x' = x + 1

Spec == Init /\ [][Next]_x

TypeOK == x \in Nat
Bounded == x <= THREE
StutterAfterThree == [](x >= THREE => UNCHANGED x)
====