------------------------------ MODULE Clock ------------------------------
EXTENDS Naturals

VARIABLES hour

HourType == hour \in 1..12

Init == hour = 1

Next ==
  /\ hour' = IF hour = 12 THEN 1 ELSE hour + 1

vars == <<hour>>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

THEOREM HourTypeInvariant:
  Spec => [] HourType

THEOREM InfiniteAdvancingSteps:
  Spec => []<>(Next)

THEOREM EachHourInfinitelyOften:
  Spec => \A i \in 1..12 : []<>(hour = i)