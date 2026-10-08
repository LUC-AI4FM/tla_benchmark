------------------------------- MODULE RollingDeployment -----------------------------

EXTENDS Integers, FiniteSets

CONSTANTS 
    Servers  \* A finite set of servers

VARIABLES 
    updating, \* Set of servers currently being updated
    available \* Set of servers currently serving requests

Init == /\ updating = {}
        /\ available = Servers

Next ==
    \/ /\ E s \in (Servers \ updating) : 
            \* Coordinator selects a server to update
           \/ /\ available' = available \ {s}
              /\ updating' = updating \cup {s}
        \/ /\ E s \in updating :
            \* Update process completes on a server
           \/ /\ available' = available \cup {s}
              /\ updating' = updating \ {s}

Spec ==
    /\ Init
    /\ [][Next]_<<updating, available>>
    /\ WF_<<updating, available>>(Next)

\* No two updates can occur simultaneously on the same server
Invariant1 == \A s \in Servers : \/ s \notin updating \/ Cardinality(updating) = 1

\* All servers are eventually updated and restored to availability
Termination == <>(available' = Servers /\ updating' = {})

=============================================================================