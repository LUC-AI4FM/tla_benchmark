---------------------------- MODULE MC_LiveHourClock ----------------------------
EXTENDS Naturals

VARIABLE
    \* @type: Int;
    hr

\* Definitions of the underlying LiveHourClock specification

HCini == hr \in (1 .. 12)

HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

HC == HCini /\ [][HCnxt]_hr

LSpec == HC /\ WF_hr(HCnxt)

TypeOK == hr \in (1 .. 12)

\* The clock eventually reaches every hour value
AlwaysTick == \A n \in 1 .. 12 : []<>(hr = n)

AllTimes == \A n \in 1 .. 12 : []<>(hr = n)

THEOREM LSpec => []HCini
=================================================================================