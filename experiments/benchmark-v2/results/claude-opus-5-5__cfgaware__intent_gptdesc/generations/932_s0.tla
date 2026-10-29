---- MODULE HourClock ----
EXTENDS Naturals

VARIABLE hr

vars == << hr >>

Hours == 1..12

TypeOK == hr \in Hours

HCini == hr \in Hours

Tick == hr' = IF hr = 12 THEN 1 ELSE hr + 1

Set(h) == /\ h \in Hours
          /\ hr' = h

SetAny == \E h \in Hours : Set(h)

HCnxt == Tick \/ SetAny

HC == HCini /\ [][HCnxt]_hr

Spec == HC /\ WF_hr(Tick)

HCInv == hr \in 1..12

WrapAround == [][(hr = 12 /\ Tick) => hr' = 1]_hr

TickCorrect == [][Tick => hr' = (IF hr = 12 THEN 1 ELSE hr + 1)]_hr

ReachAll == \A h \in Hours : []<>(hr = h)

CanReach(h, k) == \E n \in 0..11 : ((h - 1 + n) % 12) + 1 = k

StronglyConnected == \A h, k \in Hours : CanReach(h, k)

THEOREM HC => []HCInv
====