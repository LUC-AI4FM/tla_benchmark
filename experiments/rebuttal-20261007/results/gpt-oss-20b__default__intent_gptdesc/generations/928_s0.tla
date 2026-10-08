MODULE SimpleClock
EXTENDS Naturals, Integers

VARIABLE clock

Init ==
    clock ∈ 1..12

NextStep1 ==
    /\ clock' = IF clock < 12 THEN clock + 1 ELSE 1

NextStep2 ==
    /\ clock' = ((clock - 1) % 12) + 1

Next == NextStep1 /\ NextStep2

ValidHour == clock ∈ 1..12

EquivInvariant ==
    [] (IF clock < 12 THEN clock + 1 ELSE 1) = ((clock - 1) % 12) + 1

Spec == Init /\ [][Next]_clock

Safety == [] ValidHour
Liveness == []<>(clock' = IF clock < 12 THEN clock + 1 ELSE 1)