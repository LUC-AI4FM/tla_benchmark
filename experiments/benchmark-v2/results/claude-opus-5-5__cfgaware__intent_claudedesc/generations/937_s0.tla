---------------------------- MODULE LiveHourClock ----------------------------
EXTENDS Naturals

VARIABLE hr

(* Base hour-clock definitions (the contents of the HourClock module) *)
HCini == hr \in (1 .. 12)

HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

HC == HCini /\ [][HCnxt]_hr

(* Live specification: weak fairness on the tick action *)
LSpec == HC /\ WF_hr(HCnxt)

(* Properties *)
AlwaysTick == []<><<HCnxt>>_hr

AllTimes == \A n \in 1..12 : []<>(hr = n)

TypeInvariance == []HCini

THEOREM LSpec => AlwaysTick /\ AllTimes /\ TypeInvariance
=============================================================================