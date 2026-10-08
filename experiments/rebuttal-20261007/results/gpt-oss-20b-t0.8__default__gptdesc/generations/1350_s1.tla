MODULE SingleCounter
EXTENDS Naturals, TLC

VARIABLE x

Init ==
    x = 1

Next ==
    IF x < 5 THEN
        x' = x + 1
    ELSE
        x' = x

Spec ==
    Init /\ []WF(Next) /\ [] (x >= 1 /\ x <= 5)
          /\ [] (x = 1 => <>[] (x = 5))