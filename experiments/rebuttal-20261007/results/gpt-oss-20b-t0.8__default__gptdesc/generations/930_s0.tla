MODULE TwelveHourClock
EXTENDS Naturals

VARIABLE hr

Init   ==  hr \in 1..12

HCini  ==  hr \in 1..12

Next   ==
    /\ hr' = IF hr = 12 THEN 1 ELSE hr + 1

Spec   ==  Init /\ [][Next]_hr

THEOREM InvariantMaintained == Spec => [] HCini