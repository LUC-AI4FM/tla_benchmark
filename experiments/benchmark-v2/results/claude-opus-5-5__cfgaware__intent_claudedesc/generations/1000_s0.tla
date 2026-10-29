---------------------------- MODULE SimpleAllocator ----------------------------
EXTENDS FiniteSets, TLC

CONSTANTS Clients, Resources

ASSUME IsFiniteSet(Resources)

VARIABLES
  unsat,  \* unsat[c] = set of resources requested by c but not yet allocated
  alloc   \* alloc[c] = set of resources currently held by c

vars == <<unsat, alloc>>

TypeInvariant ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]

\* Resources that no client currently holds.
available == Resources \ (UNION {alloc[c] : c \in Clients})

Init ==
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]

\* A client with no outstanding request and no held resources requests a
\* nonempty set of resources.
Request(c, S) ==
  /\ unsat[c] = {}
  /\ alloc[c] = {}
  /\ S # {}
  /\ unsat' = [unsat EXCEPT ![c] = S]
  /\ UNCHANGED alloc

\* The allocator gives client c a nonempty subset of the requested resources
\* that are currently available. The request may be only partly fulfilled.
Allocate(c, S) ==
  /\ S # {}
  /\ S \subseteq (available \cap unsat[c])
  /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = @ \ S]

\* Client c returns a nonempty subset of the resources it holds.
Return(c, S) ==
  /\ S # {}
  /\ S \subseteq alloc[c]
  /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
  /\ UNCHANGED unsat

Next ==
  \E c \in Clients, S \in SUBSET Resources :
     Request(c, S) \/ Allocate(c, S) \/ Return(c, S)

SimpleAllocator ==
  /\ Init
  /\ [][Next]_vars
  /\ \A c \in Clients : WF_vars(unsat[c] = {} /\ Return(c, alloc[c]))
  /\ \A c \in Clients : SF_vars(\E S \in SUBSET Resources : Allocate(c, S))

-----------------------------------------------------------------------------
\* Properties

ResourceMutex ==
  \A c1, c2 \in Clients : c1 # c2 => alloc[c1] \cap alloc[c2] = {}

ClientsWillReturn ==
  \A c \in Clients : (unsat[c] = {}) ~> (alloc[c] = {})

ClientsWillObtain ==
  \A c \in Clients, r \in Resources : (r \in unsat[c]) ~> (r \in alloc[c])

InfOftenSatisfied ==
  \A c \in Clients : []<>(unsat[c] = {})

=============================================================================