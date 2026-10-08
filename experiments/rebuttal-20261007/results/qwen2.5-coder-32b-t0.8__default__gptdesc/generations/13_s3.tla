------------------------------- MODULE RollingDeployment ------------------------------
EXTENDS TLC, Sequences, FiniteSets

CONSTANTS 
    Servers,  \* The set of servers
    UpdateTime \* The time required to update a server

VARIABLES 
    updating,  \* Set of servers currently being updated
    offline    \* Set of servers currently offline

Init == 
    /\ updating = {}
    /\ offline = {}

Next ==
    \/ \* Coordinator process: Take a server offline, trigger update, wait for completion, and bring it back online
       /\ \E s \in Servers \ (offline \cup updating) :
            /\ offline' = offline \cup {s}
            /\ updating' = updating \cup {s} \ {s}
    \/ \* Server update process: Update a server and mark it as not updating
       /\ \E s \in updating : 
            /\ updating' = updating \ {s}

Spec ==
    WF_next(Init, Next) /\
    <>[]<<(\A s \in Servers : s \notin updating) >>  \* All servers eventually finish updating

=============================================================================