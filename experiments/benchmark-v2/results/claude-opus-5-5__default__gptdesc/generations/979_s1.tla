------------------------------- MODULE MCTwoPhase -------------------------------
EXTENDS Naturals

------------------------------- MODULE TwoPhase --------------------------------
CONSTANTS XInit(_), XAct(_, _, _)

VARIABLES p, c, x

vars == <<p, c, x>>

Init == /\ p = 0
        /\ c = 0
        /\ XInit(x)

ProducerStep == /\ p = c
                /\ XAct(0, x, x')
                /\ p' = (p + 1) % 2
                /\ c' = c

ConsumerStep == /\ p # c
                /\ XAct(1, x, x')
                /\ c' = (c + 1) % 2
                /\ p' = p

Next == ProducerStep \/ ConsumerStep

Spec == Init /\ [][Next]_vars

TypeInv == /\ p \in {0, 1}
           /\ c \in {0, 1}
================================================================================