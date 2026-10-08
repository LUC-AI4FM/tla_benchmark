----------------------------- MODULE NextStateConstraint -----------------------------

EXTENDS Naturals

VARIABLES x

Allowed(n) ==
  /\ n \in 0..9
  /\ \E k \in Nat: n = 2 * k

Init == x = 0

Next == Allowed(x')

Vars == << x >>
vars == << x >>

Spec == Init /\ [][Next]_x

=====================================================================================