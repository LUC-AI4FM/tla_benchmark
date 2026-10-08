---------------------------- MODULE Clock12Hour ----------------------------

EXTENDS Integers

CONSTANT HC

ASSUME HC = 1..12

VARIABLE hour

HCini == hour \in HC

Next == hour' = IF hour = 12 THEN 1 ELSE hour + 1

Spec == HCini /\ [][Next]_hour /\ WF_hour(Next)

TypeInvariant == hour \in HC

SafetyInvariant == hour >= 1 /\ hour <= 12

FunctionalCorrectness == [][hour' = ((hour - 1) + 1) % 12 + 1]_hour

NoDeadlock == ENABLED Next

Liveness == \A h \in HC : []<>(hour = h)

=============================================================================