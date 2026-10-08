---------------------------- MODULE SimpleAllocator ----------------------------
EXTENDS FiniteSets, Naturals

CONSTANTS Clients, Resources

VARIABLES unsat, alloc

vars == <<unsat, alloc>>

TypeInvariant ==
    /\ unsat \in [Clients -> SUBSET Resources]
    /\ alloc \in [Clients -> SUBSET Resources]

Available ==
    Resources \ (UNION {alloc[c] : c \in Clients})

Init ==
    /\ unsat = [c \in Clients |-> {}]
    /\ alloc = [c \in Clients |-> {}]

Request(c, S) ==
    /\ S # {}
    /\ S \subseteq Resources
    /\ alloc[c] = {}
    /\ unsat[c] = {}
    /\ unsat' = [unsat EXCEPT ![c] = S]
    /\ UNCHANGED alloc

Allocate(c, S) ==
    /\ S # {}
    /\ S \subseteq Available
    /\ S \subseteq unsat[c]
    /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \cup S]
    /\ unsat' = [unsat EXCEPT ![c] = unsat[c] \ S]

Return(c, S) ==
    /\ S # {}
    /\ S \subseteq alloc[c]
    /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \ S]
    /\ UNCHANGED unsat

Next ==
    \E c \in Clients :
        \/ \E S \in SUBSET Resources : Request(c, S)
        \/ \E S \in SUBSET Resources : Allocate(c, S)
        \/ \E S \in SUBSET Resources : Return(c, S)

FullReturn(c) == Return(c, alloc[c])

FullAllocate(c) == \E S \in SUBSET Resources : Allocate(c, S)

SimpleAllocator ==
    /\ Init
    /\ [][Next]_vars
    /\ \A c \in Clients : WF_vars(FullReturn(c))
    /\ \A c \in Clients : SF_vars(FullAllocate(c))

ReturnAfterSatisfied(c) ==
    /\ unsat[c] = {}
    /\ alloc[c] # {}
    /\ Return(c, alloc[c])

SimpleAllocator2 ==
    /\ Init
    /\ [][Next]_vars
    /\ \A c \in Clients : WF_vars(ReturnAfterSatisfied(c))
    /\ \A c \in Clients : SF_vars(FullAllocate(c))

ResourceMutex ==
    \A c1, c2 \in Clients : c1 # c2 => alloc[c1] \cap alloc[c2] = {}

ClientsWillReturn ==
    \A c \in Clients : (unsat[c] = {} /\ alloc[c] # {}) ~> (alloc[c] = {})

ClientsWillObtain ==
    \A c \in Clients : \A r \in Resources : r \in unsat[c] ~> r \in alloc[c]

InfOftenSatisfied ==
    \A c \in Clients : []<>(unsat[c] = {} /\ alloc[c] = {})

THEOREM SimpleAllocator => []TypeInvariant
THEOREM SimpleAllocator => []ResourceMutex
THEOREM SimpleAllocator => ClientsWillReturn
THEOREM SimpleAllocator => ClientsWillObtain
THEOREM SimpleAllocator => InfOftenSatisfied

THEOREM SimpleAllocator2 => []TypeInvariant
THEOREM SimpleAllocator2 => []ResourceMutex
THEOREM SimpleAllocator2 => ClientsWillReturn

=============================================================================