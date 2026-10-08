---- MODULE SimpleAllocator ----

CONSTANTS Clients, Resources

VARIABLES alloc, unsat

Init == /\ alloc = [c \in Clients |-> {}]
        /\ unsat = [c \in Clients |-> {}]

Request(c, S) ==
    /\ c \in Clients
    /\ S \subseteq Resources
    /\ S /= {}
    /\ alloc[c] = {}
    /\ unsat[c] = {}
    /\ UNCHANGED <<alloc EXCEPT [c \<- S], unsat>>

Allocate(c, S) ==
    /\ c \in Clients
    /\ S \subseteq (Resources \ (DOMAIN alloc))
    /\ S \subseteq unsat[c]
    /\ S /= {}
    /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \cup S]
    /\ unsat' = [unsat EXCEPT ![c] = unsat[c] \ S]
    /\ UNCHANGED (Clients \ {c})

Return(c, S) ==
    /\ c \in Clients
    /\ S \subseteq alloc[c]
    /\ S /= {}
    /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \ S]
    /\ UNCHANGED unsat

Next == 
    \/ \E c \in Clients, S \subseteq Resources : Request(c, S)
    \/ \E c \in Clients, S \subseteq (Resources \ (DOMAIN alloc)) : Allocate(c, S)
    \/ \E c \in Clients, S \subseteq alloc[c] : Return(c, S)

Spec == Init /\ [][Next]_<<alloc, unsat>>

SimpleAllocator ==
    Spec
    /\ WF_next(Return)
    /\ SF_next(Allocate)
    /\ TypeInvariant
    /\ ResourceMutex
    /\ ClientsWillReturn
    /\ ClientsWillObtain
    /\ InfOftenSatisfied

SimpleAllocator2 ==
    Spec
    /\ SF_next(Allocate)
    /\ TypeInvariant
    /\ ResourceMutex
    /\ ClientsWillReturn

TypeInvariant ==
    /\ \A c \in Clients : alloc[c] \subseteq Resources
    /\ \A c \in Clients : unsat[c] \subseteq Resources

ResourceMutex ==
    \A r \in Resources, c1, c2 \in Clients :
        c1 /= c2 => alloc[c1][r] = FALSE \/ alloc[c2][r] = FALSE

ClientsWillReturn ==
    \A c \in Clients : <>(alloc[c] = {})

ClientsWillObtain ==
    \A c \in Clients, r \in Resources :
        unsat[c][r] => <>[alloc[c][r]]_<<alloc>>

InfOftenSatisfied ==
    \A c \in Clients :
        [](unsat[c] = {}) => <>(\E r \in Resources : alloc[c][r])

WF_next(act) == \/ act \/ []<>act

SF_next(act) == <>([]act)

====