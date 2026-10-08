---- MODULE SingleIntND ----
EXTENDS Naturals, Integers

CONSTANTS N, InitVal

VARIABLES x

Domain == 0..N

TypeOK == x \in Domain

Init == x = InitVal

UnconditionalSet == x' = 0

RangeUpdate == x' \in 1..3

GuardedUpdate ==
  \/ (x = 2 /\ x' \in {1, 2, 3})
  \/ (x = N /\ x' = 0)

OutOfBoundsChoice ==
  \/ x' = -1
  \/ x' \in (N + 1)..(N + 2)

Next == UnconditionalSet \/ RangeUpdate \/ GuardedUpdate \/ OutOfBoundsChoice

Spec == Init /\ [][Next]_x

Inv == TypeOK /\ x = InitVal
====