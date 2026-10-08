------------------------------- MODULE SmallSystem -------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS F

VARIABLES x

F == [1 |-> 2, 2 |-> 3, 3 |-> 4, 4 |-> 5, 5 |-> 1]

Init == x \in {1, 2, 3, 4, 5}

N ==
  CASE x = 1 -> x' \in {F[x], F[F[x]]}
  [] x = 2 -> x' \in {F[x]}
  [] x = 3 -> x' \in {F[x], F[F[x]], F[F[F[x]]]}
  [] OTHER -> x' = x

Next == \/ N
        \/ x' = x

Spec == Init /\ [][Next]_<<x>>

Inv == x \in {1, 2, 3, 4, 5} /\ x = F[F[F[F[F[x]]]]]

=============================================================================