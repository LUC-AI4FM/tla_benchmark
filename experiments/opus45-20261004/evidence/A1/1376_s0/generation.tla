---------------------------- MODULE spec ----------------------------

CONSTANT Data

VARIABLE state

Init == state = {}

Next == \E d \in Data : state' = state \cup {d}

=======================================================================