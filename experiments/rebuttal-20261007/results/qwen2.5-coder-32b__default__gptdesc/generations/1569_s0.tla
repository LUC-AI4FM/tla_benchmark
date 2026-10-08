------------------------------- MODULE Bakery -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N \* Number of processes
ASSUME N \in Nat /\ N > 0

VARIABLES choosing, number, local_maxima, next_process, control_location

Init == 
    /\ choosing = [p \in 1..N -> FALSE]
    /\ number = [p \in 1..N -> 0]
    /\ local_maxima = [p \in 1..N -> 0]
    /\ next_process = [p \in 1..N -> 1]
    /\ control_location = [p \in 1..N -> "entry"]

Next == 
    \/ \E p \in 1..N : 
        (control_location[p] = "entry" /\ 
         choosing' = [choosing EXCEPT ![p] = TRUE] /\
         local_maxima' = [local_maxima EXCEPT ![p] = Max(number)] /\
         number' = [number EXCEPT ![p] = local_maxima[p] + 1] /\
         control_location' = [control_location EXCEPT ![p] = "request"])
    \/ \E p \in 1..N : 
        (control_location[p] = "request" /\ 
         next_process' = [next_process EXCEPT ![p] = next_process[p] + 1] /\
         control_location' = [control_location EXCEPT ![p] = IF next_process[p] > N THEN "critical_section" ELSE "request"])
    \/ \E p \in 1..N : 
        (control_location[p] = "critical_section" /\ 
         choosing' = [choosing EXCEPT ![p] = FALSE] /\
         control_location' = [control_location EXCEPT ![p] = "exit"])
    \/ \E p \in 1..N : 
        (control_location[p] = "exit" /\ 
         next_process' = [next_process EXCEPT ![p] = 1] /\
         control_location' = [control_location EXCEPT ![p] = "entry"])

Spec == Init /\ [][Next]_<<choosing, number, local_maxima, next_process, control_location>>

\* Safety properties
MutualExclusion == \A p, q \in 1..N : 
    \/ p = q 
    \/ control_location[p] /= "critical_section" 
    \/ control_location[q] /= "critical_section"

\* State constraint for TLC model checking
StateConstraint == \A p \in 1..N : number[p] \leq N

Invariant == MutualExclusion /\ StateConstraint

SpecWithInvariants == Spec /\ WF_next(Next) /\ Invariant

=============================================================================