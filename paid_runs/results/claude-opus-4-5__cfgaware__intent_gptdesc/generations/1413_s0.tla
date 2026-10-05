---------------------------- MODULE specification ----------------------------

CONSTANT InitValue

VARIABLE state

TypeOK == state \in BOOLEAN

Init == state = InitValue

Next == UNCHANGED state

Spec == Init /\ [][Next]_state /\ WF_state(Next)

Proposition == state = TRUE

AlwaysTrue == <>Proposition => <>[](Proposition)

THEOREM Spec => AlwaysTrue

=============================================================================