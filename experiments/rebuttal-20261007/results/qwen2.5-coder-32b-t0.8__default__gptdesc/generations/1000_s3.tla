------------------------------- MODULE ResourceAllocator -------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS 
    Resources,  \* Set of resources
    Clients     \* Set of clients

VARIABLES 
    heldBy,      \* Function mapping resources to the client holding them or {}
    requestedBy  \* Function mapping resources to the set of clients requesting them

Init == /\ heldBy = [r \in Resources |-> {}]
        /\ requestedBy = [r \in Resources |-> {}]

Next ==
    \/ \E r \in Resources, c \in Clients \ (DOMAIN heldBy) :
         /\ requestedBy' = [requestedBy EXCEPT ![r] = requestedBy[r] \cup {c}]
         /\ UNCHANGED <<heldBy>>
    \/ \E r \in Resources, c \in Clients : 
         /\ c \in requestedBy[r]
         /\ heldBy[r] = {}
         /\ requestedBy' = [requestedBy EXCEPT ![r] = requestedBy[r] \ {c}]
         /\ heldBy' = [heldBy EXCEPT ![r] = c]
    \/ \E r \in Resources, c \in Clients :
         /\ heldBy[r] = c
         /\ heldBy' = [heldBy EXCEPT ![r] = {}]
         /\ UNCHANGED <<requestedBy>>

Spec ==
    /\ Init
    /\ [][Next]_<<heldBy, requestedBy>>
    
TypeOK ==
    /\ DOMAIN heldBy = Resources
    /\ DOMAIN requestedBy = Resources
    /\ \A r \in Resources : heldBy[r] \in Clients \/ heldBy[r] = {}
    /\ \A r \in Resources : requestedBy[r] \subseteq Clients

MutualExclusion ==
    \A r \in Resources, c1, c2 \in Clients :
        heldBy[r] = c1 => \A r' \in Resources \ {r} : heldBy[r'] # c1
    
EventualReturn ==
    WF_<<requestedBy>> (Next)

EventualObtainment ==
    SF_<<requestedBy>> (Next)

NoUnsatisfiedRequestInfinitelyOften ==
    <>[] (\E r \in Resources : requestedBy[r] = {})

Symmetry ==
    LET permClients == [c \in Clients |-> CHOOSE c' \in Clients \\ {c}] IN
        /\ heldBy' = [r \in Resources |-> CASE \E c \in Clients : heldBy[r] = c -> permClients[heldBy[r]]
                                                   [] OTHER -> heldBy[r]]
        /\ requestedBy' = [r \in Resources |-> {permClients[c] : c \in requestedBy[r]}]

ConcreteCounterexample ==
    << 
        [r1 |-> {}, r2 |-> {}],
        [r1 |-> {}, r2 |-> {}]
    >>

=============================================================================