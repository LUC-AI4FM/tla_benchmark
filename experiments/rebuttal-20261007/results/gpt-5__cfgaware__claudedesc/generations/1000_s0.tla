----------------------------- MODULE Allocator -----------------------------

CONSTANTS
  Clients,
  Resources

VARIABLES
  unsat, \* outstanding (not-yet-allocated) requested resources per client
  alloc  \* resources currently allocated per client

vars == << unsat, alloc >>

TypeInvariant ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]
  /\ \A c \in Clients: unsat[c] \cap alloc[c] = {} \* by construction, allocated items are removed from unsat

ResourceMutex ==
  \A c \in Clients:
    \A d \in Clients:
      c /= d => alloc[c] \cap alloc[d] = {}

Init ==
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]

Avail ==
  Resources \ UNION { alloc[c] : c \in Clients }

Satisfied(c) == unsat[c] = {}

Request(c, S) ==
  /\ c \in Clients
  /\ S \subseteq Resources
  /\ S /= {}
  /\ unsat[c] = {}
  /\ alloc[c] = {}
  /\ unsat' = [unsat EXCEPT ![c] = S]
  /\ alloc' = [alloc EXCEPT ![c] = {}]

Allocate(c, S) ==
  /\ c \in Clients
  /\ S \subseteq Avail
  /\ S \subseteq unsat[c]
  /\ S /= {}
  /\ unsat' = [unsat EXCEPT ![c] = unsat[c] \ S]
  /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \cup S]

Return(c, S) ==
  /\ c \in Clients
  /\ S \subseteq alloc[c]
  /\ S /= {}
  /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \ S]
  /\ UNCHANGED unsat

\* Convenience actions quantifying the resource subset
AllocateSome(c) == \E S \in SUBSET Resources: Allocate(c, S)
ReturnSome(c)   == \E S \in SUBSET Resources: Return(c, S)

\* Full-return actions used in fairness conditions
ReturnAll(c) ==
  /\ c \in Clients
  /\ alloc[c] /= {}
  /\ alloc' = [alloc EXCEPT ![c] = {}]
  /\ UNCHANGED unsat

ReturnAllWhenSatisfied(c) ==
  /\ c \in Clients
  /\ Satisfied(c)
  /\ alloc[c] /= {}
  /\ alloc' = [alloc EXCEPT ![c] = {}]
  /\ UNCHANGED unsat

Next ==
  \/ \E c \in Clients, S \in SUBSET Resources: Request(c, S)
  \/ \E c \in Clients: AllocateSome(c)
  \/ \E c \in Clients: ReturnSome(c)

\* Liveness properties
ClientsWillReturn ==
  \A c \in Clients: []( Satisfied(c) => <> (alloc[c] = {}) )

ClientsWillObtain ==
  \A c \in Clients: []( (unsat[c] /= {}) => <> Satisfied(c) )

InfOftenSatisfied ==
  \A c \in Clients: []<> Satisfied(c)

\* Principal specification: weak fairness on full returns, strong fairness on allocations
SimpleAllocator ==
  Init
  /\ [][Next]_vars
  /\ (\A c \in Clients: WF_vars(ReturnAll(c)))
  /\ (\A c \in Clients: SF_vars(AllocateSome(c)))

\* Weaker variant: only require full returns once the request is fully satisfied
SimpleAllocator2 ==
  Init
  /\ [][Next]_vars
  /\ (\A c \in Clients: WF_vars(ReturnAllWhenSatisfied(c)))
  /\ (\A c \in Clients: SF_vars(AllocateSome(c)))

\* Theorems (for documentation; no proofs supplied)
THEOREM SimpleAllocator => []TypeInvariant
THEOREM SimpleAllocator => []ResourceMutex

\* The weaker variant preserves eventual return of resources after satisfaction,
\* but need not ensure the stronger liveness properties.
THEOREM SimpleAllocator2 => ClientsWillReturn
THEOREM ~(SimpleAllocator2 => ClientsWillObtain)
THEOREM ~(SimpleAllocator2 => InfOftenSatisfied)

=============================================================================