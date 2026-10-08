------------------------------- MODULE SmallSystem -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS DomainF, DomainN

VARIABLES x

DomainF == {1, 2, 3, 4, 5}
DomainN == {1, 2, 3}

F[1] == 2
F[n \in {2,3,4}] == F[n-1] + 1
F[5] == 1

N[i \in DomainN] == [x' \in DomainF |-> IF x' = F[x] THEN TRUE ELSE FALSE]

Init == x \in DomainF

Next == \E i \in DomainN : N[i]

Spec ==
  /\ Init
  /\ [][Next]_<<x>>

Inv == x \in DomainF /\ x = F[x]

=============================================================================