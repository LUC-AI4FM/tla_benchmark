----------------------------- MODULE HigherOrderOperatorDemo -----------------------------

EXTENDS Integers

CONSTANTS Dummy

VARIABLES v

Filter(S, P(_), Q(_, _)) ==
  { x \in S : P(x) /\ Q(x, TRUE) }

Init ==
  v \in Filter(
         {1, 2, 3, 4, 5},
         LAMBDA x: x > 1,
         LAMBDA x, b: /\ b = TRUE /\ (x % 2) = 1
       )

Next ==
  UNCHANGED v

Spec ==
  Init /\ [][Next]_v

==============================