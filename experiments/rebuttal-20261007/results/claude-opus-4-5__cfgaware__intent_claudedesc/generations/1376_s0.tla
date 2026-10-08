---------------------------- MODULE MonotonicSet ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS Data

VARIABLES dataSet

vars == <<dataSet>>

TypeOK == dataSet \subseteq Data

Init == dataSet = {}

Add(d) == 
    /\ d \in Data
    /\ d \notin dataSet
    /\ dataSet' = dataSet \cup {d}

Next == \E d \in Data : Add(d)

Spec == Init /\ [][Next]_vars

=============================================================================