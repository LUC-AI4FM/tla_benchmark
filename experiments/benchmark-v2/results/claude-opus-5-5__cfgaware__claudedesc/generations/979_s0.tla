---------------------------- MODULE MCTwoPhase ----------------------------
EXTENDS Naturals

VARIABLES p, c, x

vars == <<p, c, x>>

XInit(v) == v = 0

XAct(i, xInit, xNext) == xNext = xInit

\* Definitions of the TwoPhase specification, with XInit and XAct
\* substituted by the definitions above.

Init == /\ p = 0
        /\ c = 0
        /\ XInit(x)

ProducerStep == /\ p = c
                /\ p' = (p + 1) % 2
                /\ c' = c
                /\ XAct(0, x, x')

ConsumerStep == /\ p # c
                /\ c' = (c + 1) % 2
                /\ p' = p
                /\ XAct(1, x, x')

Next == ProducerStep \/ ConsumerStep

Spec == Init /\ [][Next]_vars

Inv == /\ p \in {0, 1}
       /\ c \in {0, 1}
       /\ x = 0
=============================================================================