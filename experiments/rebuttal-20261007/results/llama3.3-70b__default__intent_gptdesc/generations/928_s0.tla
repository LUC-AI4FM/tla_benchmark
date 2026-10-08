```
MODULE Clock
EXTENDS Integers

CONSTANTS HourSet
VARIABLES hour, nextHourMod

Init == (hour \in 1..12) /\ nextHourMod = hour

Next == (* Increment or wrap *)
        \/ hour = 12
          /\ hour' = 1
        \/ hour \in 1..11
          /\ hour' = hour + 1
        (* Equivalent modular arithmetic formulation *)
        /\ nextHourMod' = (hour + 1) % 12
        /\ IF hour = 12 THEN nextHourMod' = 1 ELSE nextHourMod' = hour + 1

Spec == Init /\ [][Next]_<<hour, nextHourMod>>

THEOREM Spec => []hour \in 1..12
THEOREM Spec => <>[]hour = 1
THEOREM Spec => <>[]hour = 2
THEOREM Spec => <>[]hour = 3
THEOREM Spec => <>[]hour = 4
THEOREM Spec => <>[]hour = 5
THEOREM Spec => <>[]hour = 6
THEOREM Spec => <>[]hour = 7
THEOREM Spec => <>[]hour = 8
THEOREM Spec => <>[]hour = 9
THEOREM Spec => <>[]hour = 10
THEOREM Spec => <>[]hour = 11
THEOREM Spec => <>[]hour = 12

THEOREM Spec => hour' = nextHourMod'
```