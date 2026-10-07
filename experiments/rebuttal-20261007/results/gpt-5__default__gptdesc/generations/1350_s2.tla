----------------------------- MODULE CounterToFive -----------------------------

EXTENDS Naturals

CONSTANTS Start, Max

ASSUME /\ Start = 1
       /\ Max = 5
       /\ Start \in Nat
       /\ Max \in Nat
       /\ Start < Max

VARIABLES x

Init ==
  x = Start

Inc ==
  /\ x < Max
  /\ x' = x + 1

StayMax ==
  /\ x = Max
  /\ x' = Max

Next ==
  Inc \/ StayMax

Spec ==
  /\ Init
  /\ [][Next]_x
  /\ WF_x(Next)

TypeInv ==
  x \in Nat

BoundsInv ==
  /\ Start <= x
  /\ x <= Max

Safety ==
  [](TypeInv /\ BoundsInv)

Liveness ==
  <>[](x = Max)

THEOREM Spec => Safety
THEOREM Spec => Liveness

===============================================================================