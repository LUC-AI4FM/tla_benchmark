---------------------------- MODULE StableBoolean ----------------------------
EXTENDS Booleans

VARIABLES state

TypeInvariant == state \in BOOLEAN

Init == state = TRUE

Next == state' = state

Spec == Init /\ [][Next]_state /\ WF_state(Next)

AlwaysTrue == state = TRUE

NextEnabled == ENABLED Next

Liveness == []NextEnabled
----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
THEOREM Spec => []AlwaysTrue
THEOREM Spec => Liveness
=============================================================================