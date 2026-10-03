------------------------------- MODULE ResourceAllocator -------------------------------

CONSTANTS 
    Resources,          \* Finite set of resources
    Clients             \* Set of clients

VARIABLES 
    heldBy,             \* Function from resources to clients (or NULL if unheld)
    requestedBy         \* Partial function from clients to sets of resources

ASSUME 
    FINITE Resources /\ FINITE Clients

CONSTANTS 
    Init                \* Initial predicate

Init == 
    /\ heldBy = [r \in Resources |-> NULL]
    /\ requestedBy = {}

VARIABLES
    pc                  \* Program counter for fairness

Next ==
    \/ \E c \in Clients, r \in Resources \ (DOMAIN requestedBy):
        /\ requestedBy' = [requestedBy EXCEPT ![c] = {r}]
        /\ heldBy' = heldBy
        /\ pc' = pc + 1
    \/ \E c \in Clients, r \in requestedBy[c]:
        /\ requestedBy' = [requestedBy EXCEPT ![c] = requestedBy[c] \ {r}]
        /\ heldBy' = [heldBy EXCEPT ![r] = c]
        /\ pc' = pc + 1
    \/ \E c \in Clients, r \in Resources:
        /\ requestedBy'[c] = {}
        /\ heldBy' = [heldBy EXCEPT ![r] = NULL]
        /\ pc' = pc + 1

Spec ==
    Init /\ [][Next]_<<pc>>

TypeOK ==
    /\ heldBy \in [Resources -> Clients \/ {NULL}]
    /\ requestedBy \in [Clients -> SUBSET Resources]

MutualExclusion ==
    \A r \in Resources: 
        LET holders == {c \in Clients | heldBy[c] = r}
        IN  Cardinality(holders) <= 1

EventualReturn ==
    \A c \in Clients, r \in Resources:
        <>[] (heldBy[r] = NULL)

EventualObtainment ==
    \A c \in Clients, r \in requestedBy[c]:
        <>[] (heldBy[r] = c)

NoUnsatisfiedRequestsInfinitelyOften ==
    []<>(requestedBy = {})

Fairness ==
    WF_next(pc)

THEOREM Spec => []TypeOK
THEOREM Spec => []MutualExclusion
THEOREM Spec => EventualReturn
THEOREM Spec => EventualObtainment
THEOREM Spec => NoUnsatisfiedRequestsInfinitelyOften

Symmetry == 
    \A perm \in [Clients -> Clients] :
        (/\ \A c1, c2 \in Clients: c1 /= c2 => perm[c1] /= perm[c2])
        => 
        (Spec
         <-> [][Next]_<<pc>>
             /\ Init
             /\ WF_next(pc)
             /\ (\A r \in Resources:
                 LET holders == {c \in Clients | heldBy[c] = r}
                 IN  Cardinality(holders) <= 1)
             /\ (\A c \in Clients, r \in requestedBy[c]:
                 <>[] (heldBy[r] = perm[c]))
             /\ (\A c \in Clients, r \in Resources:
                 <>[] (heldBy[r] = NULL))
             /\ []<>(requestedBy = {}))

ConcreteCounterexample ==
    [ heldBy |-> [r \in Resources |-> NULL],
      requestedBy |-> [c \in Clients |-> {}],
      pc |-> 0 ]

=============================================================================