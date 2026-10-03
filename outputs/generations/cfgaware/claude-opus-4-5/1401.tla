---------------------------- MODULE specification ----------------------------

VARIABLE outerX

Inner == INSTANCE InnerModule WITH x <- outerX

Init == outerX = 0

Next == Inner!Step \/ (ENABLED Inner!Step = FALSE /\ UNCHANGED outerX)

Spec == Init /\ [][Next]_outerX /\ WF_outerX(Inner!Step)

Prop == <>(outerX = 3)

=============================================================================