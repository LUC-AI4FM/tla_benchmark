----------------------------- MODULE CounterToFive -----------------------------

EXTENDS Naturals, Integers

CONSTANT Target
ASSUME Target = 5

VARIABLES x

Init ==
  x = 1

Next ==
  IF x < Target
    THEN x' = x + 1
    ELSE x' = x

vars == << x >>

TypeOK ==
  x \in Nat

BoundsInv ==
  x \in 1..Target

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Next)

Safety ==
  [](TypeOK /\ BoundsInv)

Live ==
  <>[](x = Target)

=============================================================================