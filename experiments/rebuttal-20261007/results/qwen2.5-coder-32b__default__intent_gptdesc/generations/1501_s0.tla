------------------------------- MODULE CounterSystem -------------------------------
EXTENDS Naturals, TLC

CONSTANTS 
    SMALL_CONSTANT \* e.g., 3
    LARGE_CONSTANT \* e.g., 9

VARIABLES counter

SMALL_FACTORIAL == LET n == SMALL_CONSTANT IN
                     IF n = 0 THEN 1 ELSE (n * SMALL_FACTORIAL[n - 1])

LARGE_FACTORIAL == LET n == LARGE_CONSTANT IN
                     IF n = 0 THEN 1 ELSE (n * LARGE_FACTORIAL[n - 1])

Init == counter = 0

Next == \/ /\ counter' = SMALL_FACTORIAL
        \/ /\ counter' = LARGE_FACTORIAL

Spec == Init /\ [][Next]_<<counter>>

\* Safety properties
InvCounterValues == counter \in {SMALL_FACTORIAL, LARGE_FACTORIAL}

\* Liveness properties
WF_ShortUpdates == WF_<<counter>>(/\ counter' = SMALL_FACTORIAL)
WF_LongUpdates  == WF_<<counter>>(/\ counter' = LARGE_FACTORIAL)

SpecWithProperties == Spec /\ InvCounterValues /\ WF_ShortUpdates /\ WF_LongUpdates

=============================================================================