------------------------------- MODULE RollingDeployment -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS 
    Servers  \* The set of servers

VARIABLES 
    updating,  \* Set of servers currently being updated
    down      \* Set of servers currently taken out of the load balancer

Init == /\ updating = {}
        /\ down = {}

Next ==
    \/ (* Coordinator: Take a server down, update it, and bring it back up *)
       ( /\ EXIST s \in Servers \ (updating \cup down) :
          /\ 'down' = down \ {s}
          /\ 'updating' = updating \cup {s}
        )
    \/ (\* Update process: Mark an update as complete *)
       ( /\ EXIST s \in updating :
          /\ 'down' = down
          /\ 'updating' = updating \ {s}
        )

Spec ==
    /\ Init
    /\ [][Next]_<<down, updating>>
    /\ WF_<<down, updating>>[Next]

\* Invariants: No server can be both updating and down at the same time
Inv ==
    /\ updating \cap down = {}

Termination ==
    []<>(/\ updating = {}
           /\ down = {})

=============================================================================