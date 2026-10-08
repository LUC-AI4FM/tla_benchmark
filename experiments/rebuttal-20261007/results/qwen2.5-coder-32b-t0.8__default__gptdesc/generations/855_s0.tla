------------------------------- MODULE PrisonersAndSwitches -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS 
    Prisoners,  \* Set of all prisoners
    Counter     \* The designated counter prisoner

VARIABLES 
    visited,   \* Set of prisoners who have visited the room
    switchA    \* State of switch A (BOOLEAN)

Init == /\ visited = {}
        /\ switchA = FALSE

Next ==
    \/ \/ CHOOSE p \in Prisoners : TRUE \notin visited \/\
           (p = Counter -> 
               /\ IF switchA THEN visited' = visited \cup {p} ELSE visited' = visited
               /\ switchA' = FALSE
           )
          []
            p \in Prisoners \ {Counter} -> 
                /\ visited' = visited \cup {p}
                /\ (switchA' = ~switchA) \/ switchA'
                
Spec == WF_next(Init, Next) /\ SF_next(Init, Next)

\* Safety property: When the protocol declares completion, every prisoner has visited the room
Safety == /\ Counter \in visited 
          /\ Cardinality(visited) = Cardinality(Prisoners)

\* Liveness property: The declaration condition is eventually reached
Liveness == <>(Cardinality(visited) = Cardinality(Prisoners))

=============================================================================