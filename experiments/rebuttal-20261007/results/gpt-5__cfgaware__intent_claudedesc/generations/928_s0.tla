------------------------------ MODULE HourClockEquiv ------------------------------

EXTENDS Integers

VARIABLE hr

HCBase == INSTANCE HourClock WITH hr <- hr

AltNext == hr' = (hr % 12) + 1

HC  == HCBase!HC
HC2 == HCBase!Init /\ [][AltNext]_hr

THEOREM HC_Equivalence == HC <=> HC2

===============================================================================