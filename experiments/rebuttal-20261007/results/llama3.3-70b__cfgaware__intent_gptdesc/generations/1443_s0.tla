---------------------------- MODULE Spec ----------------------------
EXTENDS Integers

CONSTANT State

VARIABLE current

Init == (current = 0)

Next == (current' = (current + 1) % 3)

Spec == Init /\ [][Next]_current

THEOREM Spec => []((current = 0) \/ (current = 1) \/ (current = 2))
THEOREM Spec => <><<current = 1>>_
THEOREM Spec => <><<current = 2>>_
THEOREM Spec => <><<current = 2>>_ /\ <><<current' = 0>>_
THEOREM Spec => []<>((current = 0) /\ (current' = 1)) /\ []<>((current = 1) /\ (current' = 2)) /\ []<>((current = 2) /\ (current' = 0))
====================================================================