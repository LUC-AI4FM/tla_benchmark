---------------------------- MODULE StationarySystem ----------------------------
EXTENDS Booleans

VARIABLES flag

Init == flag = TRUE

Next == UNCHANGED flag

Spec == Init /\ [][Next]_flag

TypeInvariant == flag \in BOOLEAN

FlagAlwaysTrue == flag = TRUE

NextEnabled == ENABLED Next

=============================================================================