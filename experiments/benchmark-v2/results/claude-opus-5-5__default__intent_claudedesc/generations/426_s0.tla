---- MODULE MinimalSpec ----
EXTENDS Naturals

CONSTANTS InitValue

VARIABLES state

vars == << state >>

Init == state = InitValue

Next == UNCHANGED state

Spec == Init /\ [][Next]_vars

TypeOK == state = InitValue

====