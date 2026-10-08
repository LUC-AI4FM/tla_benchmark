------------------------------- MODULE ClockSpecification -------------------------------

CONSTANTS HC, HC2

VARIABLES hour

HC == 1..12

HC2 == {h \in HC}

Next ==
    \/ /\ hour' = IF hour < 12 THEN hour + 1 ELSE 1
    \/ /\ hour' = (hour % 12) + 1

Spec ==
    VARIABLES hour
    INIT: hour \in HC
    NEXT: Next

Inv ==
    hour \in HC

Progress ==
    [](<>[] (hour' # hour))

Equivalence ==
    []((hour' = IF hour < 12 THEN hour + 1 ELSE 1) => (hour' = (hour % 12) + 1))
    /\ []((hour' = (hour % 12) + 1) => (hour' = IF hour < 12 THEN hour + 1 ELSE 1))

THEOREM Spec => [](Inv)
THEOREM Spec => Progress
THEOREM Spec => Equivalence

=============================================================================