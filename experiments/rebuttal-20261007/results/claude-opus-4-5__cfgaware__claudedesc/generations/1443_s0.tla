---------------------------- MODULE spec ----------------------------
EXTENDS Naturals, TLC

VARIABLE x

Init == x = 0

Next == x' = (x + 1) % 3

Spec == Init /\ [][Next]_x /\ WF_x(Next)

AllDone == x = 2

AtOne == x = 1

WrapAround == x = 2 /\ x' = 0

PossibleCounts ==
    LET stats == TLCGet("all:named")
    IN /\ stats["AllDone"] = 1
       /\ stats["AtOne"] = 1
       /\ stats["WrapAround"] = 1

=====================================================================