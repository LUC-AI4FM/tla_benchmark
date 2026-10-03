---- MODULE main ----
EXTENDS Integers, TLC

CONSTANTS

VARIABLES outerX

LOCAL MODULE InnerModule
    EXTENDS Integers
    VARIABLE x

    step == /\ x < 3
            /\ x' = x + 1
END MODULE

I == INSTANCE InnerModule WITH x <- outerX

Init == outerX = 0

Next ==
    \/ I!step
    \/ (UNCHANGED outerX /\ ~ENABLED I!step)

Fairness == WF_outerX(I!step)

Liveness == <>(outerX = 3)

Spec == Init /\ [][Next]_outerX /\ Fairness

=============================================================================