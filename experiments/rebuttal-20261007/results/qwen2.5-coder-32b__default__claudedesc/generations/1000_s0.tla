------------------------------- MODULE SimpleAllocator -------------------------------
EXTENDS TLC, FiniteSets

CONSTANTS Clients, Resources
VARIABLES alloc, unsat

Init == 
  /\ alloc = [c \in Clients |-> {}]
  /\ unsat = [c \in Clients |-> {}]

Request(c, S) ==
  \/ c \notin Clients
  \/ S = {}
  \/ alloc[c] # {}
  \/ unsat[c] # {}
  \/ unsat' = [unsat EXCEPT ![c] = S]
  \/ alloc' = alloc

Allocate(c, S) ==
  \/ c \notin Clients
  \/ S = {}
  \/ S \cap (Resources \ {r \in Resources : \E cl \in Clients: r \in alloc[cl]}) = {}
  \/ unsat[c] = {}
  \/ alloc' = [alloc EXCEPT ![c] = alloc[c] \cup S]
  \/ unsat' = [unsat EXCEPT ![c] = unsat[c] \ S]

Return(c, S) ==
  \/ c \notin Clients
  \/ S = {}
  \/ S \cap alloc[c] = {}
  \/ alloc' = [alloc EXCEPT ![c] = alloc[c] \ S]
  \/ unsat' = unsat

Next == 
  \/ \E c \in Clients, S \subseteq Resources : Request(c, S)
  \/ \E c \in Clients, S \subseteq Resources : Allocate(c, S)
  \/ \E c \in Clients, S \subseteq Resources : Return(c, S)

TypeInvariant ==
  /\ alloc \in [Clients -> SUBSET Resources]
  /\ unsat \in [Clients -> SUBSET Resources]

ResourceMutex ==
  \A r \in Resources: Cardinality({c \in Clients: r \in alloc[c]}) <= 1

ClientsWillReturn ==
  \A c \in Clients, S \subseteq Resources:
    <>(alloc[c] = {})

ClientsWillObtain ==
  \A c \in Clients, r \in Resources:
    unsat[c] /= {} /\ r \in unsat[c] => <>(r \in alloc[c])

InfOftenSatisfied ==
  \A c \in Clients:
    [](unsat[c] = {}) => <>[](alloc[c] = {})

SimpleAllocator ==
  Init /\ [][Next]_<<alloc, unsat>> /\ WF_next(Allocate) /\ SF_next(Return)

SimpleAllocator2 ==
  Init /\ [][Next]_<<alloc, unsat>> /\ WF_next(Allocate) /\ SF_next(\E c \in Clients: alloc[c] = {} => Return(c, alloc[c]))

=============================================================================