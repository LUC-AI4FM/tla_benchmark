------------------------------ MODULE HourClockExtended ------------------------------
EXTENDS Naturals, TLC

CONSTANTS 
    HC, HCnxt, hr

VARIABLES 
    hour

Init == HC /\ (hour \in 1..12)

Next == HCnxt

Spec == Init /\ [][Next]_<<hr>>

WF_hr_HCnxt == WF_hr(Next)

TickInfinitelyOften == <>[](HCnxt)

HourValuesRecursInfinitely == 
    /\ <>(hour = 1)
    /\ <>(hour = 2)
    /\ <>(hour = 3)
    /\ <>(hour = 4)
    /\ <>(hour = 5)
    /\ <>(hour = 6)
    /\ <>(hour = 7)
    /\ <>(hour = 8)
    /\ <>(hour = 9)
    /\ <>(hour = 10)
    /\ <>(hour = 11)
    /\ <>(hour = 12)

InitialTypingCondition == [] Init

LSpec == Spec /\ WF_hr_HCnxt /\ TickInfinitelyOften /\ HourValuesRecursInfinitely /\ InitialTypingCondition

THEOREM LSpec => TickInfinitelyOften /\ HourValuesRecursInfinitely /\ InitialTypingCondition

=============================================================================