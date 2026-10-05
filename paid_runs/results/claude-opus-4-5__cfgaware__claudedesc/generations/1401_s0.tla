---------------------------- MODULE Github725b ----------------------------

VARIABLE outerX

Inner725b(x) ==
    INSTANCE Inner725b WITH x <- x

Svc == Inner725b(outerX)

Init == outerX = 0

Step == Svc!Step \/ (~ ENABLED Svc!Step /\ UNCHANGED outerX)

Spec == Init /\ [][Step]_outerX /\ Svc!Fairness

Prop == <>(outerX = 3)

=============================================================================