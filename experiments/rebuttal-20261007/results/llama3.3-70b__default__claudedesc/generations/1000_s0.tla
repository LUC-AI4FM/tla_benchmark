```tla
MODULE SimpleAllocator

EXTENDS Integers, FiniteSets

CONSTANTS Clients, Resources

VARIABLES unsat, alloc

Init ==
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]

Request(c, S) ==
  /\ c \in Clients
  /\ S \subseteq Resources
  /\ S /= {}
  /\ unsat[c] = {}
  /\ alloc[c] = {}
  /\ unsat' = [unsat EXCEPT ![c] = S]
  /\ alloc' = alloc

Allocate(c, S) ==
  /\ c \in Clients
  /\ S \subseteq Resources
  /\ S /= {}
  /\ S \subseteq (Resources \cup {r \in Resources: r \notin \cup {alloc[x]: x \in Clients}})
  /\ S \subseteq unsat[c]
  /\ unsat' = [unsat EXCEPT ![c] = unsat[c] \ S]
  /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \cup S]

Return(c, S) ==
  /\ c \in Clients
  /\ S \subseteq Resources
  /\ S /= {}
  /\ S \subseteq alloc[c]
  /\ unsat' = unsat
  /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \ S]

Next ==
  \/ \E c \in Clients, S \subseteq Resources : Request(c, S)
  \/ \E c \in Clients, S \subseteq Resources : Allocate(c, S)
  \/ \E c \in Clients, S \subseteq Resources : Return(c, S)

TypeInvariant ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]

ResourceMutex ==
  /\ \A r \in Resources : \A c1, c2 \in Clients : 
    /\ c1 /= c2
    /\ r \in alloc[c1]
    ==> r \notin alloc[c2]

Spec == Init /\ [][Next]_unsat,alloc

SimpleAllocator == Spec
                   /\ WF_vars(<<c, S | c \in Clients /\ S \subseteq Resources>> : Return(c, S))
                   /\ SF_vars(<<c, S | c \in Clients /\ S \subseteq Resources>> : Allocate(c, S))

SimpleAllocator2 == Spec
                    /\ WF_vars(<<c, S | c \in Clients /\ S \subseteq Resources /\ unsat[c] = {}>> : Return(c, S))
                    /\ SF_vars(<<c, S | c \in Clients /\ S \subseteq Resources>> : Allocate(c, S))

ClientsWillReturn == \A c \in Clients : []<>unsat[c] = {}
ClientsWillObtain == \A c \in Clients, r \in Resources : <>[](r \in alloc[c])
InfOftenSatisfied == \A c \in Clients : []<><>unsat[c] = {}

THEOREM SimpleAllocator => ClientsWillReturn
THEOREM SimpleAllocator => ClientsWillObtain
THEOREM SimpleAllocator => InfOftenSatisfied
THEOREM SimpleAllocator2 => ClientsWillReturn

ASSUME Clients = {1, 2, 3}
ASSUME Resources = {a, b}

```
Note: The `ASSUME` statements at the end are used to configure the model with three clients and two resources as specified.