------------------------------ MODULE CyclicCounter ------------------------------

EXTENDS Naturals

VARIABLES state

S == {0, 1, 2}

Succ(x) == IF x = 0 THEN 1 ELSE IF x = 1 THEN 2 ELSE 0

Init == state = 0

Next == state' = Succ(state)

Spec == Init /\ []Next

(*
 Properties to be checked
*)

TypeOK == state \in S

Safety == [](state \in S)

Determinism == [](state' = Succ(state))

Reach1 == <>(state = 1)

Reach2 == <>(state = 2)

WrapAround == <>(state = 2 /\ state' = 0)

CycleLiveness == []<>(state = 0) /\ []<>(state = 1) /\ []<>(state = 2)

=============================================================================