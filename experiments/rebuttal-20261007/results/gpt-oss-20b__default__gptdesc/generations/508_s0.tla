MODULE SmallPlusCal
EXTENDS Integers

VARIABLES x, pc

Init == /\ x \in 1..10
        /\ pc = "Start"

Next ==
  \/ /\ pc = "Start"
     /\ x^2 <= 100
     /\ pc' = "Done"
     /\ x' = x
  \/ /\ pc = "Done"
     /\ pc' = "Done"
     /\ x' = x

Inv == /\ x \in 1..10
        /\ pc \in {"Start","Done"}

Spec == Init /\ [][Next]_vars /\ Inv /\ <> (pc = "Done")