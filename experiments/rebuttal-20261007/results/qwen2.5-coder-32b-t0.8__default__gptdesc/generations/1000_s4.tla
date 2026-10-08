```tla
MODULE ResourceAllocator

EXTENDS TLC, Integers, FiniteSets, Sequences

CONSTANTS 
    Clients,                    \* Set of all clients
    Resources                   \* Set of all resources

VARIABLES 
    requests,                   \* Function mapping each client to a set of requested but not yet fully satisfied resources
    heldResources               \* Function mapping each client to a set of currently held resources

Init == 
    /\ requests = [c \in Clients |-> {}]
    /\ heldResources = [c \in Clients |-> {}]

Next ==
    \/ \/ \E c \in Clients : 
            /\ requests[c] = {}
            /\ heldResources[c] = {}
            /\ \E r \in Resources :
                requests' = [requests EXCEPT ![c] = {r}]
                /\ heldResources' = heldResources
      \/ \E c \in Clients, r \in requests[c] : 
             requests' = [requests EXCEPT ![c] = requests[c] \ {r}]
             /\ heldResources' = [heldResources EXCEPT ![c] = heldResources[c] \cup {r}]
      \/ \E c \in Clients, r \in heldResources[c] :
            requests' = requests
            /\ heldResources' = [heldResources EXCEPT ![c] = heldResources[c] \ {r}]

Spec ==
    /\ Init
    /\ [][Next]_<<requests, heldResources>>

SafetyInvariant == 
    \/ \/ \A c1, c2 \in Clients :
            c1 /= c2 => (heldResources[c1] \cap heldResources[c2]) = {}
      \/ \A c \in Clients :
             (requests[c] \subseteq Resources) /\ (heldResources[c] \subseteq Resources)

LivenessInvariant ==
    \/ \/ <>[](\E c \in Clients : requests[c] = {}) 
      \/ <>(\A c \in Clients : heldResources[c] = {})
      \/ [](requests' = {} => []<>(\A r \in Resources : \A c \in Clients : r \notin requests[c]))

Fairness ==
    WF_<<requests, heldResources>>(Next)

Symmetry ==
    LET 
        perm == [c \in Clients |-> CHOOSE d \in Clients: TRUE]
    IN
        /\ (/\ c \in Clients => requests[perm[c]] = {perm[r] : r \in requests[c]})
           /\ (/\ c \in Clients => heldResources[perm[c]] = {perm[r] : r \in heldResources[c]})

ConstConstraints ==
    \/ \/ Cardinality(Clients) > 0
      \/ Cardinality(Resources) > 0

CONSTANT ConcreteCounterexampleValueStructure == 
    [ requests |-> [c \in Clients |-> {}],
      heldResources |-> [c \in Clients |-> {}]
    ]

====

```