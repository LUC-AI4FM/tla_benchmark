------------------------------ MODULE SingleCounter ------------------------------
EXTENDS Naturals, TLC

VARIABLES x

Init == 
    x = 1

Next ==
    IF x < 5 THEN
        x' = x + 1
    ELSE
        x' = x

Spec == 
    Init /\ [][Next]_x /\ WF_∅(Next)

Liveness == 
    [] (x = 1 => <> (x = 5 /\ [](x = 5)))

END MODULE