---------------------------- MODULE MC_HourClock ----------------------------
EXTENDS Naturals

VARIABLE
    \* @type: Int;
    hr

\* Definitions of the HourClock module, written inline so this module
\* parses on its own. With HourClock.tla available, they could instead
\* be imported via: INSTANCE HourClock

HCini == hr \in (1 .. 12)

HCnxt == hr' = IF hr /= 12 THEN hr + 1 ELSE 1

HC == HCini /\ [][HCnxt]_hr

=============================================================================