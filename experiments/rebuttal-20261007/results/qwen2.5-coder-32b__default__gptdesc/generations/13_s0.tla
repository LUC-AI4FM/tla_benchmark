------------------------------- MODULE RollingDeployment -------------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS 
    Servers  \* The set of servers

VARIABLES 
    updating,  \* Set of servers currently being updated
    available  \* Set of servers currently available in the load balancer

Init == /\ updating = {}
        /\ available = Servers

Next ==
    \/ \E s \in (Servers \ updating) :
        /\ updating' = updating \cup {s}
        /\ available' = available \ {s}
    \/ \E s \in updating :
        /\ updating' = updating \ {s}
        /\ available' = available \cup {s}

Spec ==
    /\ Init
    /\ [][Next]_<<updating, available>>
    /\ WF_next(<<updating, available>>)

\* Safety invariants
Invariant1 == updating \subseteq Servers  \* Updating servers are a subset of all servers
Invariant2 == available \subseteq Servers \* Available servers are a subset of all servers
Invariant3 == updating \cap available = {}  \* No server can be both updating and available

\* Liveness properties
Termination ==
    <>(updating = {})

=============================================================================