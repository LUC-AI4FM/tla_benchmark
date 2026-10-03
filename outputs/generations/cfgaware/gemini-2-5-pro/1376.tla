---- MODULE SimpleSystem ----
EXTENDS FiniteSets

CONSTANT Data

VARIABLE state

Init == state = {}

Next == \E d \in Data :
          state' = state \cup {d}

============================