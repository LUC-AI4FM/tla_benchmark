------------------------------ MODULE ResourceAllocator ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS 
    Clients,                \* Set of clients
    Resources               \* Set of resources

VARIABLES 
    heldResources,          \* Function from clients to sets of resources they hold
    requestedResources,     \* Function from clients to sets of resources they have requested
    unsatisfiedRequests     \* Function from clients to sets of resources still needed

Init == 
    /\ heldResources = [c \in Clients |-> {}]
    /\ requestedResources = [c \in Clients |-> {}]
    /\ unsatisfiedRequests = [c \in Clients |-> {}]

Next ==
    \/ \E c \in Clients, r \in Resources \ (heldResources[c] \cup requestedResources[c]) :
        /\ requestedResources' = [requestedResources EXCEPT ![c] = requestedResources[c] \cup {r}]
        /\ unsatisfiedRequests' = [unsatisfiedRequests EXCEPT ![c] = unsatisfiedRequests[c] \cup {r}]
        /\ UNCHANGED heldResources
    \/ \E c \in Clients, r \in Resources \cap (heldResources[c] \cup unsatisfiedRequests[c]) :
        /\ IF r \in heldResources[c] THEN
            /\ heldResources' = [heldResources EXCEPT ![c] = heldResources[c] \ {r}]
            /\ UNCHANGED requestedResources
            /\ UNCHANGED unsatisfiedRequests
        ELSE
            /\ unsatisfiedRequests' = [unsatisfiedRequests EXCEPT ![c] = unsatisfiedRequests[c] \ {r}]
            /\ UNCHANGED heldResources
            /\ UNCHANGED requestedResources

Spec ==
    /\ Init
    /\ [][Next]_<<heldResources, requestedResources, unsatisfiedRequests>>
    /\ <</\E c \in Clients : unsatisfiedRequests[c] = {}>>_<<heldResources, requestedResources, unsatisfiedRequests>>

SafetyProperties ==
    /\ \A c1, c2 \in Clients, r \in Resources :
        \/ c1 = c2
        \/ ~(r \in heldResources[c1] /\ r \in heldResources[c2])

LivenessProperties ==
    /\ <</\E c \in Clients : unsatisfiedRequests[c] = {}>>_<<heldResources, requestedResources, unsatisfiedRequests>>
    /\ <</\A c \in Clients, r \in Resources :
        \/ ~(r \in requestedResources[c])
        \/ <>[]<>(r \notin unsatisfiedRequests[c])>>_<<heldResources, requestedResources, unsatisfiedRequests>>

FairNext ==
    \/ \E c \in Clients, r \in Resources \ (heldResources[c] \cup requestedResources[c]) :
        /\ requestedResources' = [requestedResources EXCEPT ![c] = requestedResources[c] \cup {r}]
        /\ unsatisfiedRequests' = [unsatisfiedRequests EXCEPT ![c] = unsatisfiedRequests[c] \cup {r}]
        /\ UNCHANGED heldResources
    \/ \E c \in Clients, r \in Resources \cap (heldResources[c] \cup unsatisfiedRequests[c]) :
        /\ IF r \in heldResources[c] THEN
            /\ heldResources' = [heldResources EXCEPT ![c] = heldResources[c] \ {r}]
            /\ UNCHANGED requestedResources
            /\ UNCHANGED unsatisfiedRequests
        ELSE
            /\ unsatisfiedRequests' = [unsatisfiedRequests EXCEPT ![c] = unsatisfiedRequests[c] \ {r}]
            /\ UNCHANGED heldResources
            /\ UNCHANGED requestedResources

FairSpec ==
    /\ Init
    /\ WF_fairness
    /\ <</\E c \in Clients : unsatisfiedRequests[c] = {}>>_<<heldResources, requestedResources, unsatisfiedRequests>>

WF_fairness == 
    \/ \A c \in Clients :
        WF_[c \in Clients : <<c>>](Next)
    \/ \A r \in Resources :
        WF_[r \in Resources : <<r>>](Next)

Symmetry ==
    \A perm \in Perm(Clients) :
        /\ heldResources = [c \in Clients |-> heldResources[perm[c]]]
        /\ requestedResources = [c \in Clients |-> requestedResources[perm[c]]]
        /\ unsatisfiedRequests = [c \in Clients |-> unsatisfiedRequests[perm[c]]]

ConcreteCounterexample ==
    /\ Clients = {C1, C2}
    /\ Resources = {R1, R2}
    /\ heldResources = [C1 |-> {}, C2 |-> {}]
    /\ requestedResources = [C1 |-> {R1}, C2 |-> {R2}]
    /\ unsatisfiedRequests = [C1 |-> {R1}, C2 |-> {R2}]

=============================================================================