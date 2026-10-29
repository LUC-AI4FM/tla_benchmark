---- MODULE AssignAndGuard ----
EXTENDS Integers

VARIABLES x

vars == << x >>

Init == x = 23

Next == \E v \in {0, 1} : /\ x' = v
                          /\ x' > 0

Spec == Init /\ [][Next]_vars

TypeOK == x \in Int

NeverZero == x # 0

THEOREM Spec => [](TypeOK /\ NeverZero)
====