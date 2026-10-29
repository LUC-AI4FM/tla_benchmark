---- MODULE HourClock ----
EXTENDS Naturals

CONSTANT MaxHour

ASSUME MaxHourAssumption == MaxHour = 12

VARIABLE hr

vars == << hr >>

Hours == 1..MaxHour

ValidHour == hr \in Hours

TypeOK == ValidHour

Init == hr \in Hours

Tick ==
    hr' = IF hr < MaxHour THEN hr + 1 ELSE 1

Next == Tick

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

SafeSpec == Init /\ [][Next]_vars

HourInvariant == ValidHour

TransitionCorrect ==
    [][ \/ (hr < MaxHour /\ hr' = hr + 1)
        \/ (hr = MaxHour /\ hr' = 1) ]_vars

DeterministicStep ==
    \A h \in Hours :
        (hr = h) => (IF h < MaxHour THEN h + 1 ELSE 1) \in Hours

NoDeadlock == ENABLED Tick

AlwaysEnabled == [](ENABLED <<Next>>_vars)

KeepsTicking == []<><<Next>>_vars

EventuallyChanges == \A h \in Hours : (hr = h) ~> (hr # h)

VisitsEveryHour == \A h \in Hours : []<>(hr = h)

THEOREM TypeCorrect == Spec => []TypeOK

THEOREM InitImpliesInvariant == (Init /\ [][Next]_vars) => []ValidHour

THEOREM InductiveStep == (ValidHour /\ [Next]_vars) => ValidHour'

THEOREM TransitionCorrectness == Spec => TransitionCorrect

THEOREM NoDeadlockTheorem == Spec => []NoDeadlock

THEOREM Liveness == Spec => KeepsTicking

THEOREM Progress == Spec => EventuallyChanges

THEOREM AllHoursVisited == Spec => VisitsEveryHour
====