-------------------------------- MODULE Outer --------------------------------
EXTENDS Integers, Sequences

CONSTANTS Input

VARIABLES result, seq

Inner == INSTANCE Inner WITH result <- result, seq <- seq

Init ==
    /\ result = 0
    /\ seq = Input

Next ==
    \/ Inner!InnerNext
    \/ (ENABLED Inner!InnerNext = FALSE /\ UNCHANGED <<result, seq>>)

Spec ==
    /\ Init
    /\ [][Next]_<<result, seq>>
    /\ WF_<<result, seq>>(Inner!InnerNext)

EventuallyDisabled == <>[](ENABLED Inner!InnerNext = FALSE)

=============================================================================