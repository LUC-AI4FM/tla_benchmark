MODULE IncrementUntilFive
EXTENDS Naturals, TLC

VARIABLE x

Init == x = 1

Next ==
  \/ /\ x < 5
     /\ x' = x + 1
   \/ /\ x = 5
     /\ x' = x

Spec == Init /\ [][Next]_x /\ WF/Next

Liveness == [](x = 1 => <>[](x = 5))

ASSERTION Liveness