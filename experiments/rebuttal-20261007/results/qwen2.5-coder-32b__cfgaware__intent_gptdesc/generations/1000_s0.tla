------------------------------- MODULE ResourceAllocator -------------------------------

CONSTANTS 
    Clients,                    \* A finite set of clients
    Resources                   \* A finite set of indistinguishable resources

VARIABLES 
    heldResources,              \* Mapping from clients to subsets of Resources they hold
    outstandingRequests         \* Mapping from clients to subsets of Resources they request

ASSUME 
    Finite(Clients) /\ 
    Finite(Resources)

Init == 
    /\ heldResources = [c \in Clients |-> {}]
    /\ outstandingRequests = [c \in Clients |-> {}]

Request(c, r) == 
    /\ c \in Clients
    /\ r \subseteq Resources
    /\ r /= {}
    /\ heldResources[c] = {}
    /\ outstandingRequests[c] = {}

Grant(c, g) ==
    /\ c \in Clients
    /\ g \subseteq outstandingRequests[c]
    /\ g \subseteq (Resources \ {res \in Resources : \E cl \in Clients: res \in heldResources[cl]})
    /\ g /= {}
    
Return(c, r) == 
    /\ c \in Clients
    /\ r \subseteq heldResources[c]
    /\ r /= {}

Next ==
    \/ \E c \in Clients, r \subseteq Resources : Request(c, r)
       /\ UNCHANGED [heldResources EXCEPT ![c] = {}]
       /\ outstandingRequests' = [outstandingRequests EXCEPT ![c] = r]
    \/ \E c \in Clients, g \subseteq Resources : Grant(c, g)
       /\ heldResources' = [heldResources EXCEPT ![c] = heldResources[c] \cup g]
       /\ outstandingRequests' = [outstandingRequests EXCEPT ![c] = outstandingRequests[c] \ g]
    \/ \E c \in Clients, r \subseteq Resources : Return(c, r)
       /\ heldResources' = [heldResources EXCEPT ![c] = heldResources[c] \ r]
       /\ UNCHANGED outstandingRequests

Spec == Init /\ [][Next]_<<Clients>>

\* Safety properties
MutualExclusion ==
    \A res \in Resources : Cardinality({cl \in Clients : res \in heldResources[cl]}) <= 1

WellFormedState ==
    \A c \in Clients :
        \/ (outstandingRequests[c] = {} /\ heldResources[c] = {})
        \/ (outstandingRequests[c] /= {} /\ heldResources[c] = {})
        \/ (outstandingRequests[c] = {} /\ heldResources[c] /= {})

Safety == MutualExclusion /\ WellFormedState

\* Liveness properties
EventualAllocation ==
    \A c \in Clients : 
        WF_<<c>>(Spec) -> 
            \A r \in outstandingRequests[c] :
                <>[] (r \notin heldResources[c])

EventualReturn ==
    \A c \in Clients :
        WF_<<c>>(Spec) ->
            <>(outstandingRequests[c] = {}) -> 
                <>[](heldResources[c] = {})

RepeatedRequestSatisfaction ==
    \A c \in Clients : 
        WF_<<c>>(Spec) -> 
            <>[] (outstandingRequests[c] = {})

Liveness == EventualAllocation /\ EventualReturn /\ RepeatedRequestSatisfaction

THEOREM Spec => []Safety /\ <><>Liveness

=============================================================================