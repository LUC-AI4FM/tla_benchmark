------------------------------- MODULE ResourceAllocator -------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS 
    Resources,  \* Finite set of resources
    Clients     \* Set of clients

VARIABLES 
    held,       \* Function from Clients to subsets of Resources: resources currently held by each client
    requested   \* Function from Clients to subsets of Resources: resources currently requested but not yet fully allocated

Init == 
    /\ held = [c \in Clients |-> {}]
    /\ requested = [c \in Clients |-> {}]

Next ==
    \/ \E c \in Clients, r \in Resources \ (held[c] \cup requested[c]):
        /\ requested'[c] = requested[c] \cup {r}
        /\ held' = held
    \/ \E c \in Clients, r \in requested[c]:
        /\ requested'[c] = requested[c] \ {r}
        /\ held'[c] = held[c] \cup {r}
    \/ \E c \in Clients, r \in held[c]:
        /\ held'[c] = held[c] \ {r}
        /\ requested' = requested

Spec ==
    /\ Init
    /\ [][Next]_<<held, requested>>

TypeOK ==
    /\ \A c \in Clients: held[c] \subseteq Resources
    /\ \A c \in Clients: requested[c] \subseteq Resources
    /\ \A c \in Clients: held[c] \cap requested[c] = {}

MutualExclusion ==
    \A r \in Resources, c1, c2 \in Clients:
        c1 # c2 => ~ (r \in held[c1] /\ r \in held[c2])

EventualReturn ==
    WF_next(\E c \in Clients: held[c] /= {})

EventualObtainment ==
    WF_next(\E c \in Clients: requested[c] /= {})

NoUnsatisfiedRequestsInfinitelyOften ==
    SF_next(\A c \in Clients: requested[c] = {})

Symmetry ==
    \A perm \in [Clients -> Clients]:
        /\ perm \in PERMUTATIONS(Clients)
        => <\A c \in Clients: held'[perm[c]] = {perm[r] : r \in held[c]}>
           /\ <\A c \in Clients: requested'[perm[c]] = {perm[r] : r \in requested[c]}>

ConcreteCounterexample ==
    [held |-> [c \in Clients |-> {}],
     requested |-> [c \in Clients |-> {}]]

=============================================================================