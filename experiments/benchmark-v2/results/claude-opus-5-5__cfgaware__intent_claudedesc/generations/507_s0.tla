---------------------------- MODULE Session1 ----------------------------
EXTENDS Naturals

VARIABLES hr, count

vars == <<hr, count>>

MaxCount == 5

TypeOK ==
    /\ hr \in 1..12
    /\ count \in 0..MaxCount

Init ==
    /\ hr \in 1..12
    /\ count = 0

Tick ==
    /\ count < MaxCount
    /\ hr' = IF hr = 12 THEN 1 ELSE hr + 1
    /\ count' = count + 1

Reset ==
    /\ count = MaxCount
    /\ count' = 0
    /\ UNCHANGED hr

Next == Tick \/ Reset

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Safety ==
    /\ hr >= 1
    /\ hr <= 12
    /\ count <= MaxCount

Liveness == []<>(count = 0)

THEOREM Spec => []TypeOK
=============================================================================