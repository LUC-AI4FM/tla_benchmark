MODULE Clock12
EXTENDS Naturals, Temporal

VARIABLE hour

HourSet == 1..12

Init == hour \in HourSet

Next ==
  /\ hour' = IF hour = 12 THEN 1 ELSE hour + 1
  /\ hour' \in HourSet

Spec == Init /\ [][Next]_hour /\ Fairness(Next)

InvHourRange == hour \in HourSet

PreservesInv == InvHourRange /\ Next => InvHourRange'

FunctionalCorrectnessProp == Next

LivenessProp == ∀ i ∈ HourSet : []◇(hour = i)

LivenessUnderFair == Spec => LivenessProp