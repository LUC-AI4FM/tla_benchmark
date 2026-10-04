---------------------------- MODULE OuterCounter ----------------------------

EXTENDS Naturals

VARIABLES outerX

Inner == INSTANCE InnerCounter WITH x <- outerX

Init == outerX = 0

Next == Inner!Step \/ (ENABLED Inner!Step = FALSE /\ UNCHANGED outerX)

Spec == Init /\ [][Next]_outerX /\ WF_outerX(Inner!Step)

EventuallyThree == <>(outerX = 3)

=============================================================================