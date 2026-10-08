MODULE ConcurrentIncrement
EXTENDS Naturals, TLC

VARIABLES x, p1Done, p2Done

Init == /\ x = 0
        /\ p1Done = FALSE
        /\ p2Done = FALSE

IncP1 ==
    /\ ~p1Done
    /\ x'   = x + 1
    /\ p1Done' = TRUE
    /\ p2Done' = p2Done

IncP2 ==
    /\ ~p2Done
    /\ x'   = x + 1
    /\ p2Done' = TRUE
    /\ p1Done' = p1Done

Next == IncP1 \/ IncP2

Spec == Init /\ [][Next]_vars /\ WF(IncP1) /\ WF(IncP2)