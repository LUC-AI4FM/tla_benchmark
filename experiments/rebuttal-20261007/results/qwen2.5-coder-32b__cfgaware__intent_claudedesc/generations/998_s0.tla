------------------------------- MODULE ResourceAllocator -------------------------------

CONSTANTS 
    Clients,                      \* Finite set of clients
    Resources                     \* Finite set of resources

VARIABLES 
    heldResources,                \* Function from clients to sets of resources they hold
    requestedResources,           \* Function from clients to sets of resources they request
    schedule                      \* Ordered sequence of scheduled clients with pending requests

ASSUME 
    FINITE Clients,
    FINITE Resources

CONSTANTS 
    Init,                         \* Initial predicate
    Next,                         \* State transition relation
    Spec                          \* Complete specification

Init == 
    /\ heldResources = [c \in Clients |-> {}]
    /\ requestedResources = [c \in Clients |-> {}]
    /\ schedule = <<>>

Next ==
    \/ \E c \in Clients : 
        /\ requestedResources[c] /= {}
        /\ heldResources[c] = {}
        /\ Append(schedule, <<c>>) \in SUBSEQ(Clients)
        /\ schedule' = Append(schedule, <<c>>)
        /\ requestedResources' = [requestedResources EXCEPT ![c] = {}]
        /\ UNCHANGED heldResources
    \/ \E c \in Clients, r \in Resources :
        /\ r \notin heldResources[c]
        /\ r \notin UNION {heldResources[c'] : c' \in schedule}
        /\ requestedResources[c] /= {}
        /\ r \in requestedResources[c]
        /\ heldResources' = [heldResources EXCEPT ![c] = heldResources[c] \cup {r}]
        /\ UNCHANGED requestedResources
        /\ UNCHANGED schedule
    \/ \E c \in Clients, r \in Resources :
        /\ r \in heldResources[c]
        /\ requestedResources[c] = {}
        /\ heldResources' = [heldResources EXCEPT ![c] = heldResources[c] \ {r}]
        /\ UNCHANGED requestedResources
        /\ UNCHANGED schedule

Spec == 
    Init /\ [][Next]_<<heldResources, requestedResources, schedule>>

THEOREM Spec => []<>(\A c \in Clients : requestedResources[c] = {})

=============================================================================