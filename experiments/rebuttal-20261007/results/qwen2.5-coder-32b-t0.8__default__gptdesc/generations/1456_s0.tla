------------------------------- MODULE TinyStateMachine -------------------------------

EXTENDS Integers, FiniteSets, TLC

CONSTANTS Domain

VARIABLES x, y

Init == /\ x \subseteq Domain
        /\ y = {1, 2, 3}

Next == \/ /\ x' \subseteq y'
          /\ y' = y

FullSet == x = {1, 2, 3}
GainThree == (x \cup {3})' = x'

Spec == Init /\ [][Next]_<<x, y>>

THEOREM TLCGet("States") = <<{s \in SUBSET Domain : s \subseteq y}, {y}>> 
                         /\ TLCGet("Named States") = <<FullSet, GainThree>>
                         /\ TLCGet("State Constraint Violations") = 0
                         /\ TLCGet("Distinct States") = Cardinality(POWERSET({1, 2, 3}))
                         /\ TLCGet("Back to State") = 0
                         /\ TLCGet("States Generated") = Cardinality(POWERSET({1, 2, 3}))
                         /\ TLCGet("FullSet Count") = 1
                         /\ TLCGet("GainThree Count") = 2

=====================================================================================