------------------------------ MODULE LHourClock ------------------------------
EXTENDS HourClock

CONSTANTS \* none

VARIABLES hr

(* Base specification from HourClock *)
HC == HC
HCnxt == HCnxt
HCini == HCini

LSpec == HC /\ WF_action(HCnxt)

AlwaysTick == [] <> HCnxt
AllTimes  == \A n \in 1..12 : []<>(hr = n)
TypeInvariance == [] HCini

THEOREM AlwaysTick FROM LSpec
THEOREM AllTimes   FROM LSpec
THEOREM TypeInvariance FROM LSpec

=============================================================================