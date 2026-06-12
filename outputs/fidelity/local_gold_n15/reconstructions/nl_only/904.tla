---- MODULE HourClockWrapper ----
EXTENDS HourClock

CONSTANTS
    \* @type: Int
VARIABLES hr

Init == HourClock!Init

Next == HourClock!Next

Spec == HourClock!Spec
========================================