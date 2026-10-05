---------------------------- MODULE spec ----------------------------

VARIABLE outerX

Inner == INSTANCE InnerModule WITH x <- outerX

Init == outerX = 0

Next == Inner!step \/ (ENABLED Inner!step = FALSE /\ outerX' = outerX)

Fairness == WF_outerX(Inner!step)

Spec == Init /\ [][Next]_outerX /\ Fairness

Prop == <>(outerX = 3)

=============================================================================