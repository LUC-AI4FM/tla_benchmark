---------------------------- MODULE spec ----------------------------
EXTENDS Integers, Sequences

VARIABLES result, seq

Inner == INSTANCE Inner WITH result <- result, seq <- seq

Init == 
    /\ result = 0
    /\ seq = <<0, 1, 0, 1, 0>>

Next ==
    \/ Inner!Step
    \/ (~ ENABLED Inner!Step /\ UNCHANGED <<result, seq>>)

Spec == 
    /\ Init
    /\ [][Next]_<<result, seq>>
    /\ WF_<<result, seq>>(Inner!Step)

SpecRunsToEnd == <>[](~ ENABLED Inner!Step)

=============================================================================