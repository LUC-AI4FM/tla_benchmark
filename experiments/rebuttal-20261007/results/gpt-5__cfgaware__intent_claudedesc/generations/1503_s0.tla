---- MODULE HigherOrderOperators ----
EXTENDS Integers

VARIABLES x

Filter(S, U(_), B(_, _)) ==
  { e \in S : U(e) /\ B(e, TRUE) }

DemoSet ==
  Filter({1, 2, 3, 4, 5},
         LAMBDA y: y > 1,
         LAMBDA y, b: (y % 2) = 1 /\ b)

Init == x \in DemoSet

Next == UNCHANGED x
====